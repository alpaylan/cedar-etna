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

end Cedar.Etna
