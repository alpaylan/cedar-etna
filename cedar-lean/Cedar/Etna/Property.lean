/-
ETNA framework-neutral property result and runtime helpers for cedar-lean.

A property is a pure, total, owned-input function returning `PropertyResult`.
Witnesses replay frozen inputs; Plausible drives random search over the same
function.

The JSON output contract matches the Rust pipeline (workloads/Rust/*/src/bin/etna.rs):
exactly one line, exit code 0 except for argv parse errors. etna2 reads status
from JSON, not exit code.
-/

namespace Cedar.Etna

inductive PropertyResult where
  | pass
  | fail (msg : String)
  | discard
  deriving Repr, Inhabited, BEq, DecidableEq

def PropertyResult.toBool : PropertyResult → Bool
  | .pass | .discard => true
  | .fail _ => false

def PropertyResult.failMsg : PropertyResult → Option String
  | .fail m => some m
  | _ => none

structure Metrics where
  inputs : Nat := 0
  elapsedUs : Nat := 0
  deriving Repr, Inhabited

private def jsonEscape (s : String) : String :=
  let escChar (c : Char) : String :=
    match c with
    | '"'  => "\\\""
    | '\\' => "\\\\"
    | '\n' => "\\n"
    | '\r' => "\\r"
    | '\t' => "\\t"
    | c =>
      if c.toNat < 0x20 then
        let h := Nat.toDigits 16 c.toNat
        let pad := String.ofList (List.replicate (4 - h.length) '0')
        s!"\\u{pad}{String.ofList h}"
      else String.ofList [c]
  String.ofList (s.toList.flatMap (fun c => (escChar c).toList))

private def jsonStr (s : String) : String :=
  s!"\"{jsonEscape s}\""

private def jsonNullable : Option String → String
  | none => "null"
  | some s => jsonStr s

def emitJson
    (tool property status : String) (m : Metrics)
    (counterexample error : Option String) : IO Unit := do
  IO.println s!"\{\"status\":{jsonStr status},\"tests\":{m.inputs},\"discards\":0,\"time\":\"{m.elapsedUs}us\",\"counterexample\":{jsonNullable counterexample},\"error\":{jsonNullable error},\"tool\":{jsonStr tool},\"property\":{jsonStr property}}"

end Cedar.Etna
