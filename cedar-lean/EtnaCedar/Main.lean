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

open Cedar.Etna

namespace EtnaCedar

structure Outcome where
  status : String           -- "passed" | "failed" | "aborted"
  m : Metrics
  counterexample : Option String := none
  error : Option String := none

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

def runPlausible (property : String) : IO Outcome := do
  -- Minimal Plausible mode: not yet wired. Returns aborted with a clear
  -- message; the full random-search adapter is the next slice once
  -- Sampleable instances for Cedar's Spec types are written.
  return {
    status := "aborted",
    m := { inputs := 0, elapsedUs := 0 },
    error := some s!"plausible mode not yet wired for property '{property}' (skill-stage: scaffolding)"
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
