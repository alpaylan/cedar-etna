/-
Cedar property functions exercised by ETNA.

Each `property_*` is pure, total, takes owned inputs, and returns
`PropertyResult`. They are reused across the witness replay (`etna` mode) and
random search (`plausible` mode); a single property can serve multiple
variants when the same invariant catches several historical bugs.
-/

import Cedar.Etna.Property
import Cedar.Spec.Ext.Decimal
import Cedar.Spec.Ext.Datetime
import Cedar.Spec
import Cedar.Validation.RequestEntityValidator
import Cedar.Validation.Validator
import Cedar.SymCC.Encoder
import Cedar.SymCC.Decoder
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
  -- Schema.validateWellFormed iterates over `schema.environments`. If no
  -- action's appliesToPrincipal/Resource produces an environment, validation
  -- vacuously succeeds without inspecting entity entries — the bug doesn't
  -- manifest in that universe.
  if schema.environments.isEmpty then .discard
  else
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

/--
Property (level-checker completeness): for a chosen `(policies, schema, level)`
the validator should accept the policies. The witness instantiates a policy
that uses a literal entity UID equal to the environment's action in
entity-access position (`Action::"a" in Action::"a"`). Pre-#573 the level
checker had no special case for literal entity UIDs and routed them through
the `_, _ => false` fallthrough, rejecting valid policies as `.levelError`.

This is a *completeness* variant — the buggy validator is over-strict, not
unsound. We frame it as ETNA does any other variant: the witness asserts
acceptance, and the variant patch causes the witness to fail.

Historical fix: c186f0f (cedar-spec #573 "Update level checking to allow
access to literals equal to environment action"), which added the
`.lit (.entityUID euid) _, _ => euid == env.reqty.action` clause to
`TypedExpr.checkEntityAccessLevel`. The synthetic ETNA patch reduces that
clause's body to `false`, restoring the over-strict behavior.
-/
def property_validate_with_level_accepts (policies : Policies) (schema : Schema) (level : Nat) : PropertyResult :=
  match validateWithLevel policies schema level with
  | .ok () => .pass
  | .error (.levelError pid) =>
    .fail s!"validateWithLevel rejected policy {pid} with .levelError — the level checker rejected an entity-access expression it should have allowed"
  | .error _ => .pass

/--
Property (SymCC encoder soundness, empty-record edge case): the SMT-LIB
text emitted by `defineRecord tyEnc []` must not contain the malformed
empty-application form `({tyEnc} )` (a parenthesized constructor with
zero arguments and a stray internal space).

In SMT-LIB 2.7 a record literal is encoded either as the bare type
constructor (when the record has no fields) or as `(Ty f₁ f₂ … fₙ)` when
it has at least one field. The intermediate form `(Ty )` — emitted by
the buggy `defineRecord` for an empty record — is not a legal s-expression
application and downstream solvers either reject the script or, worse,
silently misparse it.

Historical fix: 7b9fe45 (cedar-spec #752 "Fix encodings of empty record
literals"), which guards on `tEncs.isEmpty` and emits the bare
constructor in that case. The synthetic ETNA patch removes the guard;
the witness then constructs an empty record and observes the malformed
`(R0 )` body in the captured SMT output.
-/
def property_encoder_empty_record_well_formed (tyEnc : String) : IO PropertyResult := do
  let bufRef ← IO.mkRef ({ data := ByteArray.empty, pos := 0 } : IO.FS.Stream.Buffer)
  let stream := IO.FS.Stream.ofBuffer bufRef
  let solver : Cedar.SymCC.Solver := { smtLibInput := stream, smtLibOutput := none }
  let state : Cedar.SymCC.EncoderState := {
    terms := Batteries.RBMap.empty,
    types := Batteries.RBMap.empty,
    uufs  := Batteries.RBMap.empty,
    enums := Batteries.RBMap.empty
  }
  let action : IO (String × Cedar.SymCC.EncoderState) :=
    ((Cedar.SymCC.Encoder.defineRecord tyEnc []).run state).run solver
  let _ ← action.toBaseIO
  let buf ← bufRef.get
  let smtText : String := String.fromUTF8! buf.data
  let badPattern : String := s!"({tyEnc} )"
  if (smtText.splitOn badPattern).length > 1 then
    return .fail s!"defineRecord {repr tyEnc} [] emitted malformed empty-application `{badPattern}` in SMT output: {repr smtText}"
  return .pass

/--
Property (SymCC encode/decode roundtrip on empty records): for any record
type `tyEnc` registered as a `TermType.record (Map.mk [])` in the
decoder's `IdMaps.types`, decoding the bare symbol `tyEnc` (the form the
encoder emits for an empty record literal per #752) must yield the empty
record term — not fail with `"enum id"`.

Pre-#721, `SExpr.decodeLit` on a bare `.symbol e` only checked
`ids.enums.find?` and failed with `"enum id"` if the symbol was not a
declared enum member. After #752 made the encoder emit bare type
constructors for empty records, models containing empty records would
crash the decoder before being interpreted, breaking any SymCC pipeline
whose policies include empty record literals.

The fix renamed the helper to `enumOrEmptyRecord` and routed the
`.none` case to `constructEntityOrRecord s []`, which resolves the
symbol against `ids.types` and constructs the empty record when the
type is registered as a record. The synthetic ETNA patch reverts that
`.none` branch to the original `fail "enum id"` form; the witness then
sees `Decoder.decodeLit ids (.symbol "R0")` return an `Except.error`
where the fixed decoder returns `Term.record (Map.mk [])`.
-/
def property_encoder_empty_record_decode_roundtrip (tyEnc : String) : PropertyResult :=
  let recordTy : Cedar.SymCC.TermType := .record (Cedar.Data.Map.mk [])
  let ids : Cedar.SymCC.Decoder.IdMaps := {
    types := Cedar.SymCC.Decoder.IdMap.ofList [(tyEnc, recordTy)],
    vars  := Cedar.SymCC.Decoder.IdMap.ofList [],
    uufs  := Cedar.SymCC.Decoder.IdMap.ofList [],
    enums := Cedar.SymCC.Decoder.IdMap.ofList []
  }
  match Cedar.SymCC.Decoder.SExpr.decodeLit ids (Cedar.SymCC.Decoder.SExpr.symbol tyEnc) with
  | Except.ok (.record (Cedar.Data.Map.mk [])) => .pass
  | Except.ok t => .fail s!"decodeLit {repr tyEnc} returned unexpected term {repr t} (expected empty record)"
  | Except.error msg => .fail s!"decodeLit {repr tyEnc} failed with `{msg}` — empty-record symbol roundtrip is broken"

/--
Property (Duration parser Int64-range round-trip): for any `Int n` whose
magnitude fits in `Int64`, `Duration.parse s!"{n}ms"` must succeed and
produce a `Duration` whose underlying `Int64` value equals `Int64.ofInt n`.

Pre-#577, `Duration.parse` first parsed the *unsigned* magnitude into
`Int64` and only then negated, so for `Int64.MIN = -9223372036854775808`
the unsigned magnitude `9223372036854775808` overflowed `Int64`
(`Int64.MAX = 9223372036854775807`) — `parseUnit?` returned `none` and
the whole parse failed, even though `Int64.MIN` is itself a valid
`Int64`. Post-fix, the negation is folded into per-unit parsing
(`Int.negOfNat` before the `Int64.ofInt?` check), so `Int64.MIN`
parses successfully.

Random search drives this with `genInt64MagnitudeAroundMin` (biased
toward magnitudes near `Int64.MIN`); the witness pins it to the
worst-case input `Int64.MIN`.
-/
def property_duration_parse_min_value (n : Int) : PropertyResult :=
  match Int64.ofInt? n with
  | none => .discard
  | some i64 =>
    let str := s!"{n}ms"
    match Datetime.Duration.parse str with
    | some d =>
      if d.val == i64 then .pass
      else .fail s!"Duration.parse {repr str} = some {repr d.val} but expected {repr i64}"
    | none => .fail s!"Duration.parse {repr str} returned none for in-range Int64 value {n}"

end Cedar.Etna
