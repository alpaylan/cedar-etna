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

open Cedar.Spec
open Cedar.Validation
open Cedar.Data

private def actionEty : EntityType := { id := "Action", path := [] }
private def userEty : EntityType   := { id := "User",   path := [] }
private def photoEty : EntityType  := { id := "Photo",  path := [] }
private def actionUid : EntityUID  := { ty := actionEty, eid := "a" }

private def aseValid : ActionSchemaEntry := {
  appliesToPrincipal := Set.mk [userEty],
  appliesToResource  := Set.mk [photoEty],
  ancestors          := Set.empty,
  context            := Map.empty,
}

/-- One-action schema: ets is empty, acts maps `Action::"a"` to a fully formed entry. -/
private def schemaWithOneAction : Schema := {
  ets  := Map.empty,
  acts := Map.mk [(actionUid, aseValid)],
}

/--
Action entity carrying a forbidden attribute. On the fixed validator,
`validateEntities` must reject this with a `typeError`; on the buggy
variant, the attrs check is skipped and validation returns `.ok ()`.
-/
private def badActionEntityData : EntityData := {
  attrs     := Map.mk [(("x" : Attr), Value.prim (.int (Int64.ofInt 1)))],
  ancestors := Set.empty,
  tags      := Map.empty,
}

private def entitiesBadAction : Entities :=
  Map.mk [(actionUid, badActionEntityData)]

def witness_decimal_parse_negative_sign_preserved_case_neg_zero : PropertyResult :=
  property_decimal_parse_negative_sign_preserved "-0.5"

def witness_decimal_parse_no_underscore_case_int_part : PropertyResult :=
  property_decimal_parse_no_underscore "1_2.34"

def witness_validate_action_entity_no_attrs_case_action_with_attr : PropertyResult :=
  property_validate_action_entity_no_attrs schemaWithOneAction entitiesBadAction

def witness_smt_encode_string_balanced_quotes_case_quote_in_middle : IO PropertyResult :=
  property_smt_encode_string_balanced_quotes "x\"y"

end Cedar.Etna
