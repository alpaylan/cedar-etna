/-
Cedar property functions exercised by ETNA.

Each `property_*` is pure, total, takes owned inputs, and returns
`PropertyResult`. They are reused across the witness replay (`etna` mode) and
random search (`plausible` mode); a single property can serve multiple
variants when the same invariant catches several historical bugs.
-/

import Cedar.Etna.Property
import Cedar.Spec.Ext.Decimal
import Cedar.Spec
import Cedar.Validation.RequestEntityValidator
import Cedar.Validation.Validator
import Cedar.SymCC.Encoder
import Cedar.Validation.EnvironmentValidator

namespace Cedar.Etna

open Cedar.Spec.Ext
open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/--
Property: a parsed decimal whose source string starts with `'-'` must not be
strictly positive.

Catches the family of decimal-parser sign-handling bugs where the parser
inferred sign from the parsed integer part rather than from the textual
prefix. With "-0.<frac>" the integer part round-trips to `0 ≥ 0`, so a sign
test on the parsed integer leaks the wrong branch and emits a positive
decimal.

Historical fix: 84fe9c6 (cedar-spec #799), which replaced
`if l ≥ 0 then l' + r' else l' - r'` with
`if !left.startsWith "-" then l' + r' else l' - r'`. Reverse-applying that
patch reintroduces the bug; the witness `"-0.5"` then yields some `0.5000`
(positive) where it should yield `-0.5000`.
-/
def property_decimal_parse_negative_sign_preserved (s : String) : PropertyResult :=
  match Decimal.parse s with
  | none => .pass
  | some d =>
    if s.startsWith "-" && d > 0 then
      .fail s!"Decimal.parse {repr s} = some {repr d} but a leading '-' must yield a non-positive decimal"
    else .pass

/--
Property: `Decimal.parse` rejects any input containing `_`.

Catches the family of decimal-parser underscore-leak bugs. Lean's
`String.toInt?` and `String.toNat?` silently accept `_` characters
(e.g. `String.toInt? "1_2" = some 12`); using them directly inside
`Decimal.parse` lets `"1_2.34"` parse to `12.3400`, which the Cedar
spec disallows.

Historical fix: a0c5812 (cedar-spec #877), later refactored into
`Cedar.Spec.Ext.Util` as `toInt?'`/`toNat?'`, which gate
`String.toInt?`/`String.toNat?` behind a `String.contains '_'` check.
Reverse-applying that patch removes the gates; the witness `"1_2.34"`
then parses where the spec says it should not.
-/
def property_decimal_parse_no_underscore (s : String) : PropertyResult :=
  match Decimal.parse s with
  | none => .pass
  | some d =>
    if s.contains '_' then
      .fail s!"Decimal.parse {repr s} = some {repr d} but underscores are disallowed"
    else .pass

/--
Property (validator soundness): if `validateEntities schema entities` returns
`.ok ()`, then every action entity in `entities` (judged by membership in any
schema environment's `acts` table) must have **empty** `attrs`.

Cedar's spec forbids action entities from carrying attributes — the
type-checker proofs of soundness rely on this invariant when reasoning about
action authorization. A validator that accepts an action entity with
non-empty `attrs` admits ill-typed worlds.

Historical fix: d7ab5ab (cedar-spec #648 "Fix validator soundness when
`updateSchema` is not used"), which folded the action-entity attrs/tags
checks directly into `instanceOfSchemaEntry` so that calling
`validateEntities` without first invoking `updateSchema` no longer leaks
the soundness gap. The synthetic ETNA patch reintroduces the gap by
short-circuiting the `data.attrs == Map.empty` guard in
`instanceOfActionSchemaEntry`.
-/
def property_validate_action_entity_no_attrs (schema : Schema) (entities : Entities) : PropertyResult :=
  match validateEntities schema entities with
  | .error _ => .pass
  | .ok () =>
    let actionUids : List EntityUID :=
      schema.environments.flatMap (fun env => env.acts.toList.map Prod.fst)
    let bad : List EntityUID := actionUids.filter (fun uid =>
      match entities.find? uid with
      | .some d => !d.attrs.toList.isEmpty
      | .none   => false)
    match bad with
    | [] => .pass
    | uid :: _ => .fail s!"validateEntities passed but action entity {uid} has non-empty attrs"

/--
Property (SMT-LIB encoding soundness): the SMT string literal produced by
wrapping `Cedar.SymCC.Encoder.encodeString s` in outer `"`...`"` must contain
an even number of `"` characters.

Per SMT-LIB 2.7, every literal `"` inside a string value must be doubled
(`""`), and the literal is delimited by outer `"` on each side. Both forms
are quote-balanced: any well-formed SMT string literal has an even count of
`"` characters.

Historical fix: 84708ca (cedar-spec #640 "Fix SMT encoding of string
literals") added the doubling rule (`s.replace "\"" "\"\""`) to
`encodeString` so user-controlled strings containing `"` produce
spec-compliant SMT. The buggy state lets a single `"` leak through,
making the resulting SMT malformed; downstream solvers either reject the
query or — worse — silently misparse it, yielding unsound symbolic
verification results.

This property runs in `IO` because `encodeString` is `IO String` (it
throws on out-of-range Unicode code points).
-/
def property_smt_encode_string_balanced_quotes (s : String) : IO PropertyResult := do
  let body ← Cedar.SymCC.Encoder.encodeString s
  let encoded := s!"\"{body}\""
  let quoteCount := encoded.toList.foldl (fun n c => if c == '"' then n + 1 else n) 0
  if quoteCount % 2 == 0 then return .pass
  else return .fail s!"encodeString({repr s}) wrapped to {repr encoded} has {quoteCount} '\"' (odd; malformed SMT)"

/--
Build a stub `Cedar.SymCC.Solver` whose streams discard everything written
and produce nothing. `defineEntity` for enum-typed entities never touches
the solver streams (it only reads from EncoderState), so a no-op solver
is sufficient for testing the enum branch.
-/
private def stubSolver : IO Cedar.SymCC.Solver := do
  let nullDev ← IO.FS.Handle.mk "/dev/null" .write
  let stream := IO.FS.Stream.ofHandle nullDev
  return { smtLibInput := stream, smtLibOutput := none }

/--
Property (SymCC encoder soundness): if `defineEntity tyEnc entity` returns
successfully for an entity whose type is registered as an enum, then
`entity.eid` must be one of the declared enum members.

Pre-#855, `defineEntity` looked up `members.idxOf entity.eid` (non-`?`
variant), which on `List` returns `members.length` when the element is
absent — producing an out-of-range enum index. The encoder then emitted
`{tyEnc}_m{members.length}` as the SMT identifier, referencing a
member that does not exist. Downstream solvers either generate UNSAT for
the wrong reason or accept an invalid model, breaking soundness.

Historical fix: fe5a046 (cedar-spec #855 "Fix escaping for euid in term
protobuf"; the Lean side replaced `idxOf` with `idxOf?` and explicitly
threw on the `none` case). The synthetic ETNA patch reverts that to the
buggy index-leak form.
-/
def property_define_entity_rejects_non_member
    (members : List String) (entity : Cedar.Spec.EntityUID) : IO PropertyResult := do
  -- Vacuously pass if the eid IS a valid member; the bug is in the absent case.
  if members.contains entity.eid then return .pass
  let state : Cedar.SymCC.EncoderState := {
    terms := Batteries.RBMap.empty,
    types := Batteries.RBMap.empty,
    uufs  := Batteries.RBMap.empty,
    enums := Batteries.RBMap.ofList [(entity.ty, members)] (compareOfLessAndEq · ·)
  }
  let solver ← stubSolver
  let action : IO (String × Cedar.SymCC.EncoderState) :=
    ((Cedar.SymCC.Encoder.defineEntity "U_enc" entity).run state).run solver
  let result ← action.toBaseIO
  match result with
  | .ok (encId, _) =>
    return .fail s!"defineEntity for non-member {entity.eid} returned {repr encId} instead of throwing (members: {members})"
  | .error _ => return .pass

/--
Property (validator entity-existence soundness): if `validate policies schema`
returns `.ok ()`, then every policy's expression must pass
`checkEntities schema · = .ok ()` — i.e. every entity UID literal and every
`is <Type>` must reference a type/uid declared in the schema.

Cedar's Lean typechecker historically short-circuited on type errors for
unknown entity types, so a policy referencing an undeclared `Foo::"x"`
passed Lean validation while the Rust validator (which runs the entity
existence check as a separate pass) rejected it. The two validators
disagreed on validity, breaking the differential-soundness contract.

Historical fix: eb3bfff (cedar-spec #779 "Make lean validator check entity
type and action existence before type checking"), which added the
`checkEntities` pre-pass at the top of `typecheckPolicyWithEnvironments`.
The synthetic ETNA patch removes that pre-pass; the witness then
constructs a policy referencing an undeclared entity type and observes
`validate` returning `.ok ()` instead of an `unknownEntity` error.

This property uses `checkEntities` itself as the soundness oracle —
validation must agree with the existence check on every policy.
-/
def property_validate_rejects_undeclared_entities (policies : Policies) (schema : Schema) : PropertyResult :=
  match validate policies schema with
  | .error _ => .pass
  | .ok () =>
    let bad : List String := policies.filterMap (fun p =>
      match checkEntities schema p.toExpr with
      | .error _ => some p.id
      | .ok () => none)
    match bad with
    | [] => .pass
    | pid :: _ => .fail s!"validate passed but policy {pid} references undeclared entities"

/--
Property (request-validation soundness): if `validateRequest schema request`
returns `.ok ()`, then `request.principal` must exist somewhere in the
schema — either as a valid entity UID in `env.ets` for some environment, or
as an action in `env.acts`.

Catches the family of bugs where `instanceOfEntityType` accepted any UID
whose entity type matched the expected one, ignoring whether the UID was
actually declared. Pre-#658, the function checked only enum membership
(returning `true` for non-enum types regardless of declaration), so a
"ghost" entity reference like `User::"ghost"` would match a request type
even with `User` absent from the entity schema. Downstream typecheckers
then treat the request as well-typed, voiding their soundness assumptions.

Historical fix: 1a76346 (cedar-spec #658 "Add `Environment.WellFormed` as
a new precondition"). The implementation change is the new check
`env.ets.isValidEntityUID e || env.acts.contains e` in
`instanceOfEntityType`. The synthetic ETNA patch replaces that conjunct
with `true`; the witness then sees a `User::"ghost"` request validate
against a schema that declares no `User` type.
-/
def property_validate_request_principal_exists (schema : Schema) (request : Request) : PropertyResult :=
  match validateRequest schema request with
  | .error _ => .pass
  | .ok () =>
    let inEts := schema.ets.isValidEntityUID request.principal
    let inActs := schema.acts.contains request.principal
    if inEts || inActs then .pass
    else .fail s!"validateRequest passed but principal {request.principal} is not declared in schema"

/--
Property (TypeEnv well-formedness): if `Schema.validateWellFormed schema`
returns `.ok ()`, then every attribute type and every tag type in every
schema entry must be lifted — i.e. no nested `.bool .tt` or `.bool .ff`
singleton-bool types are allowed; only `.bool .anyBool` is.

The Cedar typechecker's soundness proofs assume every schema-level type is
lifted, so an unlifted singleton-bool type lets the typechecker prove a
literal-specific judgement (`flag : bool .tt`) on user-provided attribute
data, which is unsound under the actual operational semantics (the user
can put `flag = false` in an entity). The fix added a `validateLifted`
pass over schema-level types in `StandardSchemaEntry.validateWellFormed`
and `ActionSchemaEntry.validateWellFormed`.

Historical fix: e785e2e (cedar-spec #689 "Require that well-formed
TypeEnv does not have singleton Bool types"). The synthetic ETNA patch
removes the `(CedarType.record entry.attrs).validateLifted` line; the
witness then constructs a schema whose entity attribute has type
`.bool .tt` and observes `Schema.validateWellFormed` returning `.ok ()`
instead of a `bool type is not lifted` error.
-/
def property_schema_well_formed_no_singleton_bools (schema : Schema) : PropertyResult :=
  match Schema.validateWellFormed schema with
  | .error _ => .pass
  | .ok () =>
    let attrsBad : List EntityType := schema.ets.toList.filterMap (fun (ety, entry) =>
      match entry with
      | .standard se =>
        match (CedarType.record se.attrs).validateLifted with
        | .error _ => some ety
        | .ok () => none
      | .enum _ => none)
    match attrsBad with
    | [] => .pass
    | ety :: _ => .fail s!"Schema.validateWellFormed passed but entity type {ety} has an unlifted (singleton-bool) attribute"

end Cedar.Etna
