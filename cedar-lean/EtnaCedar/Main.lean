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
import Cedar.Etna.Generators
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

/-! Random-search budget.
`numTrials` is a hard cap; `runtimeBudgetMs` is a soft deadline that lets the
runner emit a clean `passed` JSON before etna-cli's external timeout
SIGKILLs the process (which records `aborted` and discards counter info).
Both can be overridden via env vars so callers can tune without rebuilds:
  ETNA_RUNNER_MAX_TRIALS   — overrides numTrials
  ETNA_RUNNER_TIMEOUT_MS   — overrides runtimeBudgetMs (set ~5s below the
                              etna-cli timeout to give the runner headroom). -/
private def defaultNumTrials  : Nat := 1_000_000
private def defaultRuntimeMs  : Nat := 55_000   -- assumes ~60 s outer timeout
private def maxSize : Nat := 100

private def envNat (key : String) : IO (Option Nat) := do
  match ← IO.getEnv key with
  | none => return none
  | some s => return s.toNat?

private def getNumTrials : IO Nat := do
  return (← envNat "ETNA_RUNNER_MAX_TRIALS").getD defaultNumTrials

private def getRuntimeBudgetMs : IO Nat := do
  return (← envNat "ETNA_RUNNER_TIMEOUT_MS").getD defaultRuntimeMs

/-- Variant of `runRandomSamples` that takes an explicit `Gen` rather than
relying on the type's `SampleableExt` instance. Used for properties whose
default sampler is too unfocused (e.g. `String` for decimal-parser bugs).
Both helpers report the etna2 JSON contract: `passed` if all samples return
`.pass`/`.discard`, `failed` on the first counterexample with the offending
input rendered via `Repr`.

We bypass `Plausible.Testable.checkIO` because it requires elaboration-time
`NamedBinder` annotations from `mk_decorations`; at runtime in `IO` we drive
`Gen` directly via `Gen.run` over a `SampleableExt.interpSample` (default)
or an explicit `Gen` (this helper). -/
private def runRandomSamplesWith {α : Type} [Repr α]
    (g : Plausible.Gen α) (prop : α → PropertyResult) : IO Outcome := do
  let numTrials ← getNumTrials
  let budgetMs ← getRuntimeBudgetMs
  let t0 ← IO.monoMsNow
  let deadline := t0 + budgetMs
  let elapsedUs (t1 : Nat) : Nat := (t1 - t0) * 1000
  let mut tested : Nat := 0
  for i in [0 : numTrials] do
    if (← IO.monoMsNow) ≥ deadline then break
    let sample ← Plausible.Gen.run g (i % maxSize)
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

private def runRandomSamples {α : Type}
    [Plausible.SampleableExt α] [Repr α]
    (prop : α → PropertyResult) : IO Outcome := do
  let numTrials ← getNumTrials
  let budgetMs ← getRuntimeBudgetMs
  let t0 ← IO.monoMsNow
  let deadline := t0 + budgetMs
  let elapsedUs (t1 : Nat) : Nat := (t1 - t0) * 1000
  let mut tested : Nat := 0
  for i in [0 : numTrials] do
    if (← IO.monoMsNow) ≥ deadline then break
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
  let numTrials ← getNumTrials
  let budgetMs ← getRuntimeBudgetMs
  let t0 ← IO.monoMsNow
  let deadline := t0 + budgetMs
  let elapsedUs (t1 : Nat) : Nat := (t1 - t0) * 1000
  let mut tested : Nat := 0
  for i in [0 : numTrials] do
    if (← IO.monoMsNow) ≥ deadline then break
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
  | "EncoderEmptyRecordWellFormed" =>
      .ok witness_encoder_empty_record_well_formed_case_record_zero_fields
  | "EncoderEmptyRecordDecodeRoundtrip" =>
      .ok (pure witness_encoder_empty_record_decode_roundtrip_case_R0_zero_fields)
  | "DurationParseMinValue" =>
      .ok (pure witness_duration_parse_min_value_case_int64_min)
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

/-! Synthesize `Repr` instances for the structured Cedar types via their
existing `Repr` derivations, so the runRandomSamples helpers can stringify
counterexamples. Cedar's existing derivations cover most of these. -/

def runPlausible (property : String) : IO Outcome :=
  match property with
  | "DecimalParseNegativeSignPreserved" =>
    runRandomSamplesWith Cedar.Etna.genDecimalString property_decimal_parse_negative_sign_preserved
  | "DecimalParseNoUnderscore" =>
    runRandomSamplesWith Cedar.Etna.genDecimalString property_decimal_parse_no_underscore
  | "SmtEncodeStringBalancedQuotes" =>
    runRandomSamplesIO property_smt_encode_string_balanced_quotes
  | "ValidateActionEntityNoAttrs" =>
    runRandomSamples (fun (p : Cedar.Validation.Schema × Cedar.Spec.Entities) =>
      property_validate_action_entity_no_attrs p.fst p.snd)
  | "ValidateRejectsUndeclaredEntities" =>
    runRandomSamples (fun (p : Cedar.Spec.Policies × Cedar.Validation.Schema) =>
      property_validate_rejects_undeclared_entities p.fst p.snd)
  | "ValidateRequestPrincipalExists" =>
    runRandomSamples (fun (p : Cedar.Validation.Schema × Cedar.Spec.Request) =>
      property_validate_request_principal_exists p.fst p.snd)
  | "SchemaWellFormedNoSingletonBools" =>
    runRandomSamples property_schema_well_formed_no_singleton_bools
  | "DefineEntityRejectsNonMember" =>
    runRandomSamplesIO (fun (p : List String × Cedar.Spec.EntityUID) =>
      property_define_entity_rejects_non_member p.fst p.snd)
  | "ValidateWithLevelAccepts" =>
    runRandomSamples (fun (p : Cedar.Spec.Policies × Cedar.Validation.Schema × Nat) =>
      property_validate_with_level_accepts p.fst p.snd.fst p.snd.snd)
  | "EncoderEmptyRecordWellFormed" =>
    runRandomSamplesIO property_encoder_empty_record_well_formed
  | "EncoderEmptyRecordDecodeRoundtrip" =>
    runRandomSamplesWith Cedar.Etna.genRecordTypeName property_encoder_empty_record_decode_roundtrip
  | "DurationParseMinValue" =>
    runRandomSamplesWith Cedar.Etna.genInt64MagnitudeAroundMin property_duration_parse_min_value
  | _ => return {
      status := "aborted",
      m := {},
      error := some s!"plausible mode not wired for property '{property}'"
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
