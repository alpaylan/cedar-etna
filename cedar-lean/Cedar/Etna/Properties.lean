/-
Cedar property functions exercised by ETNA.

Each `property_*` is pure, total, takes owned inputs, and returns
`PropertyResult`. They are reused across the witness replay (`etna` mode) and
random search (`plausible` mode); a single property can serve multiple
variants when the same invariant catches several historical bugs.
-/

import Cedar.Etna.Property
import Cedar.Spec.Ext.Decimal

namespace Cedar.Etna

open Cedar.Spec.Ext

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

end Cedar.Etna
