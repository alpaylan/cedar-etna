/-
Frozen witnesses for ETNA. Each `witness_<name>_case_<tag>` calls a
`property_<name>` from `Cedar.Etna.Properties` with concrete inputs.

Contract:
- on the base tree (every patch applied), the witness must evaluate to .pass
- with `git apply -R patches/<variant>.patch` the witness must evaluate to .fail

The `#guard` checks below run at elaboration time on the base tree and
constitute the static "base passes" half of the contract; the runtime "variant
fails" half is exercised by `lake exe etna_cedar etna <Property>`.
-/

import Cedar.Etna.Properties

namespace Cedar.Etna

def witness_decimal_parse_negative_sign_preserved_case_neg_zero : PropertyResult :=
  property_decimal_parse_negative_sign_preserved "-0.5"

def witness_decimal_parse_no_underscore_case_int_part : PropertyResult :=
  property_decimal_parse_no_underscore "1_2.34"

end Cedar.Etna
