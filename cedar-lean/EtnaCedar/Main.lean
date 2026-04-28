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

def runEtna (property : String) : IO Outcome := do
  let t0 ← IO.monoMsNow
  let r : Except String PropertyResult :=
    match property with
    | "DecimalParseNegativeSignPreserved" =>
        Except.ok witness_decimal_parse_negative_sign_preserved_case_neg_zero
    | "DecimalParseNoUnderscore" =>
        Except.ok witness_decimal_parse_no_underscore_case_int_part
    | _ => Except.error s!"Unknown property for etna: {property}"
  let t1 ← IO.monoMsNow
  let elapsed : Nat := (t1 - t0) * 1000
  match r with
  | .error msg => return { status := "aborted", m := { inputs := 0, elapsedUs := elapsed }, error := some msg }
  | .ok pr =>
    match pr with
    | .pass | .discard =>
      return { status := "passed", m := { inputs := 1, elapsedUs := elapsed } }
    | .fail msg =>
      return { status := "failed", m := { inputs := 1, elapsedUs := elapsed }, counterexample := some msg }

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
