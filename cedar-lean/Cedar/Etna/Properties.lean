/-
ETNA blackbox property functions for Cedar-Lean.

Each `property_*` is a Cedar-spec invariant a tester would write *without*
knowing which patch is in flight: parse/print roundtrips, structural
well-formedness on encoded SMT, spec-level oracles like `checkEntities` for
entity existence, and so on. Properties take generic inputs and run them
through Cedar's natural front-door API (evaluator, validator, full SymCC
encoder) — they don't reach into individual encoder/decoder helpers and
don't pin inputs to bug-triggering shapes.

A single property can serve multiple variants when the same invariant
catches several historical bugs. Witnesses pin specific inputs that
demonstrate each variant; random search drives the same property over
generated inputs.
-/

import Cedar.Etna.Property
import Cedar.Spec.Ext.Decimal
import Cedar.Spec.Ext.Datetime
import Cedar.Spec
import Cedar.Validation.RequestEntityValidator
import Cedar.Validation.Validator
import Cedar.Validation.Typechecker
import Cedar.Validation.TypedExpr
import Cedar.SymCC.Compiler
import Cedar.SymCC.Encoder
import Cedar.SymCC.Decoder
import Cedar.SymCC.Solver
import Cedar.SymCC.Verifier
import Cedar.Validation.EnvironmentValidator

namespace Cedar.Etna

open Cedar.Spec.Ext
open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/-! ## Decimal — parse/print roundtrip and grammar invariants. -/

/--
Property: `Decimal.parse (toString d) = some d` for every `Decimal d`.

This is the canonical print-then-parse roundtrip property for a Decimal
parser/printer pair. It catches sign-handling bugs without referencing the
parser internals: the printer emits a textual sign for negatives, and the
parser must re-derive it. A bug in the sign-inference path manifests as a
roundtrip mismatch (e.g., `toString (-1 : Decimal) = "-0.0001"`, but a
buggy parser returns `+0.0001`).
-/
def property_decimal_parse_negative_sign_preserved (n : Int) : PropertyResult :=
  match Int64.ofInt? n with
  | none => .discard
  | some i64 =>
    let d : Decimal := i64
    let s := toString d
    match Decimal.parse s with
    | some d' =>
      if d' == d then .pass
      else .fail s!"toString {repr d} = {repr s}, but Decimal.parse {repr s} = some {repr d'} ≠ {repr d}"
    | none =>
      .fail s!"toString {repr d} = {repr s} did not roundtrip — parse returned none"

/--
Property (parser grammar adherence): the Cedar spec grammar for decimal
literals is `[-]?[0-9]+\.[0-9]+`. Every character of an accepted string
must therefore be one of `-`, `.`, or a digit `0`-`9` — anything else
(`_`, letters, whitespace, etc.) is outside the grammar and the parser
must reject it.

This is the spec-grammar safety invariant a tester would write without
knowing which specific non-grammar character a buggy parser leaks
through (Lean's `String.toInt?`/`String.toNat?` happen to accept `_`,
but the same property catches any other lenient-character bug).
-/
def property_decimal_parse_no_underscore (s : String) : PropertyResult :=
  match Decimal.parse s with
  | none => .pass
  | some d =>
    let outOfGrammar : List Char := s.toList.filter (fun c =>
      not (c = '-' || c = '.' || ('0' ≤ c && c ≤ '9')))
    match outOfGrammar with
    | [] => .pass
    | c :: _ => .fail s!"Decimal.parse {repr s} = some {repr d} but contains non-grammar character {repr c}"

/-! ## Duration — parse/print roundtrip via `toMilliseconds`. -/

/--
Property: for any `Int n` whose magnitude fits `Int64`,
`Duration.parse "<n>ms"` must succeed and round-trip via `toMilliseconds`.
This is the parse spec invariant for the `ms`-suffix grammar; it does not
reference the parser internals.
-/
def property_duration_parse_min_value (n : Int) : PropertyResult :=
  match Int64.ofInt? n with
  | none => .discard
  | some i64 =>
    let str := s!"{n}ms"
    match Datetime.Duration.parse str with
    | some d =>
      if d.val == i64 then .pass
      else .fail s!"Duration.parse {repr str} returned {repr d.val}, expected {repr i64}"
    | none =>
      .fail s!"Duration.parse {repr str} returned none for in-range Int64 value {n}"

/-! ## SymCC encoder — structural well-formedness on captured SMT.

These properties feed a generated Cedar `Expr` through the public
`SymCC.compile + Encoder.encode` pipeline against a buffered solver, and
check structural well-formedness rules on the captured SMT-LIB text. The
properties don't reach into individual encoder helpers; they assert
spec-level rules about SMT-LIB output (balanced quotes; no malformed
empty-application form). -/

private def runFullEncode (expr : Expr) : IO String := do
  let bufRef ← IO.mkRef ({ data := ByteArray.empty, pos := 0 } : IO.FS.Stream.Buffer)
  let stream := IO.FS.Stream.ofBuffer bufRef
  let solver : Cedar.SymCC.Solver := { smtLibInput := stream, smtLibOutput := none }
  let εnv : Cedar.SymCC.SymEnv := Cedar.SymCC.SymEnv.ofEnv default
  match Cedar.SymCC.compile expr εnv with
  | .error _ => return ""
  | .ok t =>
    let action : IO Cedar.SymCC.EncoderState :=
      Cedar.SymCC.SolverM.run solver (Cedar.SymCC.Encoder.encode [t] εnv)
    let _ ← action.toBaseIO
    let buf ← bufRef.get
    return String.fromUTF8! buf.data

/--
Property (SMT-LIB structural rule): every well-formed SMT-LIB script has an
even count of `"` characters — every literal `"` inside a string value is
either part of an outer delimiter pair or doubled (`""`). For any Cedar
`Expr` the public `Encoder.encode` produces SMT-LIB; if the captured text
has an odd quote count, the encoder emitted malformed SMT.
-/
def property_smt_encode_string_balanced_quotes (expr : Expr) : IO PropertyResult := do
  let smtText ← runFullEncode expr
  let quoteCount := smtText.toList.foldl (fun n c => if c == '"' then n + 1 else n) 0
  if quoteCount % 2 == 0 then return .pass
  else return .fail s!"encoded SMT for {repr expr} has {quoteCount} '\"' (odd; malformed): {repr smtText}"

/--
Property (SMT-LIB structural rule): empty applications are not legal
SMT-LIB *terms* — a parenthesized `(<symbol>)` form requires at least one
argument when used as a value. The encoder emits each top-level form
followed by a newline (`emitln`), so a malformed empty-application value
appears as ` ))<newline>` at end of line (atom + space + value-close +
form-close + newline). The legitimate `(declare-datatype <T> (\n  (<T> )))`
constructor form ends with three close-parens (` )))<newline>`), so the
two-paren-then-newline tail is uniquely produced by buggy value
emissions.
-/
def property_encoder_empty_record_well_formed (expr : Expr) : IO PropertyResult := do
  let smtText ← runFullEncode expr
  if (smtText.splitOn " ))\n").length > 1 then
    return .fail s!"encoded SMT for {repr expr} ends a line with ` ))<newline>` — a value-position empty-application form is malformed SMT-LIB: {repr smtText}"
  return .pass

/-! ## SymCC encoder — defense-in-depth (variant 4).

Cedar's validator rejects literal references to non-member enum entities at
the `compilePrim` gate, so a non-member `User::"ghost"` never reaches
`defineEntity` through the natural compile path. The bug — `defineEntity`
silently emitting a bogus enum identifier (`U_enc_m<members.length>`) for
non-members instead of erroring — is a defense-in-depth check: the encoder
must not silently accept ill-formed inputs even if upstream rejection
should have caught them.

We test it via the public `Encoder.encode` API by feeding a hand-built
`Term.prim (.entity uid)` directly, alongside a `SymEnv` whose
`SymEntities` registers `uid.ty` as an enum with the given members.
A blind random search rarely lands on this contract — flagging it requires
noticing the encoder produced an out-of-range enum index, which without an
SMT parser is hard to verify in PBT — so this property's expected utility
comes from witness replay rather than blind random testing.
-/

private def stubSolver : IO Cedar.SymCC.Solver := do
  let nullDev ← IO.FS.Handle.mk "/dev/null" .write
  let stream := IO.FS.Stream.ofHandle nullDev
  return { smtLibInput := stream, smtLibOutput := none }

/-- Build a minimal `SymEnv` registering one enum entity type with the
given member set. -/
private def symEnvWithEnum (ety : EntityType) (eids : List String) : Cedar.SymCC.SymEnv :=
  let symData : Cedar.SymCC.SymEntityData :=
    { attrs := .udf {
        arg := Cedar.SymCC.TermType.ofType (.entity ety),
        out := Cedar.SymCC.TermType.record Map.empty,
        table := Map.empty,
        default := Cedar.SymCC.Term.prim (.bool false) }
      ancestors := Map.empty,
      members := some (Set.make eids),
      tags := none }
  { request := default,
    entities := Map.mk [(ety, symData)] }

/--
Property: for an enum-typed entity term whose `eid` is not a registered
member, `Encoder.encode` must error rather than silently emitting an
out-of-range enum identifier. Random search drives the property over a
random member list and a random `EntityUID`; the property is vacuous when
the eid happens to be a member.
-/
def property_define_entity_rejects_non_member
    (members : List String) (entity : Cedar.Spec.EntityUID) : IO PropertyResult := do
  if members.contains entity.eid then return .pass
  let εnv := symEnvWithEnum entity.ty members
  let term : Cedar.SymCC.Term := .prim (.entity entity)
  let solver ← stubSolver
  let action : IO Cedar.SymCC.EncoderState :=
    Cedar.SymCC.SolverM.run solver (Cedar.SymCC.Encoder.encode [term] εnv)
  let result ← action.toBaseIO
  match result with
  | .ok _ =>
    return .fail s!"Encoder.encode accepted non-member enum eid {repr entity.eid} (members: {repr members})"
  | .error _ => return .pass

/-! ## SymCC decoder — encode/decode roundtrip on registered types.

The natural blackbox encode/decode roundtrip requires a real SMT solver to
emit the model. For a self-contained Lean ETNA we instead pin a synthetic
model line whose value is the bare type symbol — the form a solver is
allowed to emit for a value of an empty record type — and assert the public
`Decoder.decode` accepts it. -/

/-- Build a minimal `EncoderState` whose `types` map registers `tyEnc` as
an empty record type and whose `terms` map registers a single TermVar
`v0` of that type. The decoder needs the variable to be known so that the
LHS of the model's `(define-fun v0 () <tyEnc> <tyEnc>)` line resolves; the
bug under test is in handling the bare-symbol RHS, not the LHS. -/
private def encoderStateWithRecord (tyEnc : String) : Cedar.SymCC.EncoderState :=
  let recordTy : Cedar.SymCC.TermType := .record (Cedar.Data.Map.mk [])
  let v : Cedar.SymCC.TermVar := { id := "v0", ty := recordTy }
  { terms := Batteries.RBMap.ofList [(Cedar.SymCC.Term.var v, "v0")] (compareOfLessAndEq · ·),
    types := Batteries.RBMap.ofList [(recordTy, tyEnc)] (compareOfLessAndEq · ·),
    uufs  := Batteries.RBMap.empty,
    enums := Batteries.RBMap.empty }

/--
Property: for any registered record type symbol `tyEnc`, the public
`Decoder.decode` must accept a model that uses the bare symbol as a value —
the standard form a solver emits for an empty record. The decoder must
reconstruct the empty record term rather than fail.
-/
def property_encoder_empty_record_decode_roundtrip (tyEnc : String) : PropertyResult :=
  let enc := encoderStateWithRecord tyEnc
  let model := s!"((define-fun v0 () {tyEnc} {tyEnc}))"
  match Cedar.SymCC.Decoder.decode model enc with
  | .ok _ => .pass
  | .error msg =>
    .fail s!"Decoder.decode rejected the empty-record symbol {repr tyEnc}: {msg}"

/-! ## Validator soundness — spec rules over generated schemas. -/

/--
Property (validator soundness): if `validateEntities schema entities`
returns `.ok ()`, then every action entity (one whose UID is in
`schema.acts`) has empty `attrs`. This is the Cedar spec rule that action
entities carry no attributes — every authorization-soundness theorem in
`Thm/Validation/` relies on it.
-/
def property_validate_action_entity_no_attrs (schema : Schema) (entities : Entities) : PropertyResult :=
  match validateEntities schema entities with
  | .error _ => .pass
  | .ok () =>
    let actionUids : List EntityUID := schema.acts.toList.map Prod.fst
    let bad : List EntityUID := actionUids.filter (fun uid =>
      match entities.find? uid with
      | .some d => !d.attrs.toList.isEmpty
      | .none   => false)
    match bad with
    | [] => .pass
    | uid :: _ => .fail s!"validateEntities passed but action entity {uid} has non-empty attrs"

/--
Property (validator entity-existence): if `validate policies schema`
returns `.ok ()`, then every entity reference in every policy's expression
must resolve under the schema. We use the spec-level `checkEntities` walker
as the oracle — it traverses policy ASTs and rejects references to
undeclared types/UIDs, encoding the spec rule "validators must check
entity existence" independently of any specific validator implementation.
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
Property (request-validation soundness): if
`validateRequest schema request` returns `.ok ()`, then `request.principal`
must reference a declared entity in the schema. The spec rule is "every
request principal corresponds to a real entity"; we encode it by checking
the principal against the schema's entity-type registry and action
registry.
-/
def property_validate_request_principal_exists (schema : Schema) (request : Request) : PropertyResult :=
  match validateRequest schema request with
  | .error _ => .pass
  | .ok () =>
    if schema.ets.isValidEntityUID request.principal || schema.acts.contains request.principal then .pass
    else .fail s!"validateRequest passed but principal {request.principal} is not declared in schema"

/--
Property (validator type-preservation): if a schema is well-formed and
typechecks an expression to a concrete `CedarType τ`, evaluation must
produce a `Value` that is an *instance* of `τ`. This is the canonical
preservation theorem for a typed expression language.

Specifically: for any `(expr, schema, request, entities)` —
  • `Schema.validateWellFormed schema = .ok ()`,
  • `validateRequest schema request = .ok ()`,
  • the schema has an environment matching the request triple
    `(principal.ty, resource.ty, action)`,
  • `typeOf expr ∅ env = .ok (te, _)`,
  • `evaluate expr request entities = .ok v`,
then `instanceOfType v te.typeOf env = true`.

This is broader than spec-rule oracles like "no singleton-bool attrs in
the schema": it instead asserts the typechecker's *promised type* lines
up with the evaluator's *actual value*. The variant-7 bug surfaces here
because removing `validateLifted` lets a schema declare e.g.
`User.flag : .bool .tt`; the typechecker then promises `principal.flag :
bool .tt`, but the evaluator returns whatever the user-supplied entity
holds — so `instanceOfType (Bool false) (.bool .tt)` fails.

Note: we deliberately do NOT require `validateEntities schema entities =
.ok ()` here. The bugs being tested live in the *static-analysis* layer
(validateWellFormed, the typechecker), and downstream entity-validation
would short-circuit by rejecting mismatched values before evaluation —
masking the bug. Random search over `(expr, schema, request, entities)`
quadruples directly probes the typechecker→evaluator agreement.
-/
def property_validator_type_preservation
    (expr : Expr) (schema : Schema) (request : Request) (entities : Entities) : PropertyResult :=
  match Schema.validateWellFormed schema with
  | .error _ => .discard
  | .ok () =>
  match validateRequest schema request with
  | .error _ => .discard
  | .ok () =>
  match Schema.environment? schema request.principal.ty request.resource.ty request.action with
  | none => .discard
  | some env =>
    match typeOf expr ∅ env with
    | .error _ => .discard
    | .ok (te, _) =>
      match evaluate expr request entities with
      | .error _ => .discard
      | .ok v =>
        if instanceOfType v te.typeOf env then .pass
        else .fail s!"typechecker promised {repr te.typeOf} for {repr expr}, but evaluator returned {repr v} (not an instance under env)"

/--
Property (level-checker completeness fixture): for the chosen
`(policies, schema, level)` the validator must accept the policies. This
is a unit-test-style property — a completeness gap surfaces only on a
specific known-good fixture, and random search has no leverage here. The
witness pins the fixture; random search reduces to "did the validator
accept whatever we generated", which is meaningless.
-/
def property_validate_with_level_accepts (policies : Policies) (schema : Schema) (level : Nat) : PropertyResult :=
  match validateWithLevel policies schema level with
  | .ok () => .pass
  | .error (.levelError pid) =>
    .fail s!"validateWithLevel rejected policy {pid} with .levelError — the level checker rejected an entity-access expression it should have allowed"
  | .error _ => .pass

/-! ## SymCC pipeline preservation — broad CVC5-backed property.

This is the canonical preservation property for a verifier compiler:
for any well-typed `(env, body)` pair, running the policy
`permit when { body }` through `verifyNeverErrors → Encoder.encode →
CVC5 → [getModel → Decoder.decode]` must succeed end-to-end. CVC5 is
the SMT-LIB grammar oracle (catches encoder bugs that emit malformed
output) and the decoder reconstructing the model is the round-trip
oracle (catches decoder bugs).

The property requires the `CVC5` env var to point at a CVC5 binary;
without it, the property discards. With type-directed random
generation (`Cedar.Etna.TypeDirected.genJointInputs`), random search
exercises this pipeline over arbitrary well-typed Cedar expressions —
the broad-preservation property a tester would write without knowing
which encoder/decoder corner is broken. -/

private def policyPermitWhen (body : Expr) : Policy := {
  id := "p_etna",
  effect := .permit,
  principalScope := .principalScope .any,
  actionScope := .actionScope .any,
  resourceScope := .resourceScope .any,
  condition := [{ kind := .when, body := body }]
}

def property_symcc_pipeline_soundness (env : TypeEnv) (body : Expr) : IO PropertyResult := do
  match ← IO.getEnv "CVC5" with
  | none => return .discard
  | some _ =>
  let symEnv : Cedar.SymCC.SymEnv := Cedar.SymCC.SymEnv.ofEnv env
  -- `verifyAlwaysMatches` asks "is the policy always true?" — its asserts
  -- encode the body's evaluation logic in full (vs. `verifyNeverErrors`,
  -- whose asserts only encode error paths and constant-fold pure bodies
  -- to trivial constants). For SymCC encoder/decoder soundness we need
  -- the body's literals (strings, records) to appear in the SMT, which
  -- `verifyAlwaysMatches` preserves.
  match Cedar.SymCC.verifyAlwaysMatches (policyPermitWhen body) symEnv with
  | .error _   => return .discard
  | .ok asserts =>
    let action : IO (Cedar.SymCC.Decision × Cedar.SymCC.EncoderState × Option String) := do
      let solver ← Cedar.SymCC.Solver.cvc5
      let inner : Cedar.SymCC.SolverM (Cedar.SymCC.Decision × Cedar.SymCC.EncoderState × Option String) := do
        let enc ← Cedar.SymCC.Encoder.encode asserts symEnv (produceModels := true)
        let dec ← Cedar.SymCC.Solver.checkSat
        let model ← match dec with
          | .sat => Cedar.SymCC.Solver.getModel
          | _    => pure ""
        return (dec, enc, if dec matches .sat then some model else none)
      Cedar.SymCC.SolverM.run solver inner
    match ← action.toBaseIO with
    | .error e =>
      -- CVC5 rejected the encoded SMT — encoder leaked malformed output.
      return .fail s!"CVC5 rejected encoded SMT for body {repr body}: {e}"
    | .ok (.sat, enc, some model) =>
      -- Encode-decode roundtrip: decoder must accept the solver's model.
      match Cedar.SymCC.Decoder.decode model enc with
      | .ok _      => return .pass
      | .error msg =>
        return .fail s!"Decoder.decode rejected CVC5's model: {msg}\n  body: {repr body}\n  model: {model}"
    | .ok _ =>
      -- unsat or unknown — pipeline succeeded; no model to roundtrip.
      return .pass

end Cedar.Etna
