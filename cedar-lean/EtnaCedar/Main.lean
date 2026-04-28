/-
ETNA dispatcher for cedar-lean.

Invocation: `lake exe etna_cedar <tool> <Property>`
  <tool>      : etna | plausible
  <Property>  : PascalCase property name (e.g. DecimalParseNoDashOnlyIntPart) | All

Output: exactly one JSON line on stdout. Exit code 0 except for argv-parse
errors (exit 2). etna2's log_process_output reads status from JSON, never
from the exit code (project_etna_runner_json_contract memory).
-/

import Cedar.Etna.Property
import Cedar.Etna.Properties
import Cedar.Etna.Witnesses
import Plausible

open Cedar.Etna
open Plausible

namespace EtnaCedar

structure Outcome where
  status : String           -- "passed" | "failed" | "aborted"
  m : Metrics
  counterexample : Option String := none
  error : Option String := none

/-! ## Plausible random-search adapter
Properties whose inputs are primitive types (String, Nat, …) plug into
Plausible directly. Properties parameterised over Cedar's structured types
(Schema, Request, Policies, …) need Sampleable instances first; those are
left for a follow-up slice. The Plausible-mode runner enumerates only the
properties currently supported and reports `aborted` for the rest. -/

private def numTrials : Nat := 200
private def maxSize : Nat := 100

/--
Generic random-search loop for a property over a single `SampleableExt` type.
Produces an `Outcome` matching the etna2 JSON contract: `passed` if `numTrials`
samples all return `.pass` / `.discard`; `failed` on the first counterexample,
with the offending input rendered via `Repr` and the property's `.fail` message
appended.

This bypasses Plausible's high-level `Testable.checkIO`, which depends on
elaboration-time NamedBinder annotations supplied by the `mk_decorations`
tactic. At runtime in `IO` we drive `Gen` directly via `interpSample` and
`Gen.run`.
-/
private def runRandomSamples {α : Type}
    [Plausible.SampleableExt α] [Repr α]
    (prop : α → PropertyResult) : IO Outcome := do
  let t0 ← IO.monoMsNow
  let elapsedUs (t1 : Nat) : Nat := (t1 - t0) * 1000
  let mut tested : Nat := 0
  for i in [0 : numTrials] do
    let sample ← Plausible.Gen.run (Plausible.SampleableExt.interpSample α) (i % maxSize)
    tested := tested + 1
    match prop sample with
    | .pass | .discard => continue
    | .fail msg =>
      let t1 ← IO.monoMsNow
      return {
        status := "failed",
        m := { inputs := tested, elapsedUs := elapsedUs t1 },
        counterexample := some s!"({reprStr sample}) — {msg}"
      }
  let t1 ← IO.monoMsNow
  return { status := "passed", m := { inputs := tested, elapsedUs := elapsedUs t1 } }

private def runRandomSamplesIO {α : Type}
    [Plausible.SampleableExt α] [Repr α]
    (prop : α → IO PropertyResult) : IO Outcome := do
  let t0 ← IO.monoMsNow
  let elapsedUs (t1 : Nat) : Nat := (t1 - t0) * 1000
  let mut tested : Nat := 0
  for i in [0 : numTrials] do
    let sample ← Plausible.Gen.run (Plausible.SampleableExt.interpSample α) (i % maxSize)
    tested := tested + 1
    let pr ← (prop sample).toBaseIO
    match pr with
    | .ok .pass | .ok .discard => continue
    | .ok (.fail msg) =>
      let t1 ← IO.monoMsNow
      return {
        status := "failed",
        m := { inputs := tested, elapsedUs := elapsedUs t1 },
        counterexample := some s!"({reprStr sample}) — {msg}"
      }
    | .error e =>
      let t1 ← IO.monoMsNow
      return {
        status := "aborted",
        m := { inputs := tested, elapsedUs := elapsedUs t1 },
        error := some s!"property raised IO exception: {e}"
      }
  let t1 ← IO.monoMsNow
  return { status := "passed", m := { inputs := tested, elapsedUs := elapsedUs t1 } }

def witnessFor (property : String) : Except String (IO PropertyResult) :=
  match property with
  | "DecimalParseNegativeSignPreserved" =>
      .ok (pure witness_decimal_parse_negative_sign_preserved_case_neg_zero)
  | "DecimalParseNoUnderscore" =>
      .ok (pure witness_decimal_parse_no_underscore_case_int_part)
  | "ValidateActionEntityNoAttrs" =>
      .ok (pure witness_validate_action_entity_no_attrs_case_action_with_attr)
  | "SmtEncodeStringBalancedQuotes" =>
      .ok witness_smt_encode_string_balanced_quotes_case_quote_in_middle
  | "ValidateRejectsUndeclaredEntities" =>
      .ok (pure witness_validate_rejects_undeclared_entities_case_unknown_principal)
  | "ValidateRequestPrincipalExists" =>
      .ok (pure witness_validate_request_principal_exists_case_ghost_user)
  | "SchemaWellFormedNoSingletonBools" =>
      .ok (pure witness_schema_well_formed_no_singleton_bools_case_attr_bool_tt)
  | "DefineEntityRejectsNonMember" =>
      .ok witness_define_entity_rejects_non_member_case_zzz
  | "ValidateWithLevelAccepts" =>
      .ok (pure witness_validate_with_level_accepts_case_action_in_action)
  | _ => .error s!"Unknown property for etna: {property}"

def runEtna (property : String) : IO Outcome := do
  let t0 ← IO.monoMsNow
  match witnessFor property with
  | .error msg =>
    let t1 ← IO.monoMsNow
    let elapsed : Nat := (t1 - t0) * 1000
    return { status := "aborted", m := { inputs := 0, elapsedUs := elapsed }, error := some msg }
  | .ok io =>
    let pr ← (io : IO PropertyResult).toBaseIO
    let t1 ← IO.monoMsNow
    let elapsed : Nat := (t1 - t0) * 1000
    match pr with
    | .ok .pass | .ok .discard =>
      return { status := "passed", m := { inputs := 1, elapsedUs := elapsed } }
    | .ok (.fail msg) =>
      return { status := "failed", m := { inputs := 1, elapsedUs := elapsed }, counterexample := some msg }
    | .error e =>
      return { status := "aborted", m := { inputs := 1, elapsedUs := elapsed }, error := some s!"witness raised IO exception: {e}" }

def runPlausible (property : String) : IO Outcome :=
  match property with
  | "DecimalParseNegativeSignPreserved" =>
    runRandomSamples property_decimal_parse_negative_sign_preserved
  | "DecimalParseNoUnderscore" =>
    runRandomSamples property_decimal_parse_no_underscore
  | "SmtEncodeStringBalancedQuotes" =>
    runRandomSamplesIO property_smt_encode_string_balanced_quotes
  | _ => return {
      status := "aborted",
      m := {},
      error := some s!"plausible mode not wired for property '{property}' (no Sampleable instance for its input type)"
    }

def dispatch (tool property : String) : IO Outcome :=
  match tool with
  | "etna" => runEtna property
  | "plausible" => runPlausible property
  | _ => pure { status := "aborted", m := {}, error := some s!"Unknown tool: {tool}" }

end EtnaCedar

def main (args : List String) : IO UInt32 := do
  match args with
  | [tool, property] => do
    let outcome ← EtnaCedar.dispatch tool property
    Cedar.Etna.emitJson tool property outcome.status outcome.m outcome.counterexample outcome.error
    return 0
  | _ => do
    IO.eprintln "Usage: etna_cedar <tool> <Property>"
    IO.eprintln "Tools: etna | plausible"
    return 2
