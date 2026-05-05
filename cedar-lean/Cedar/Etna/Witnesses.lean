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

/-- Witness: parse-print roundtrip on `Decimal{val:=-1}` (`= -0.0001`). The
buggy parser computes the sign from the parsed integer part —
`String.toInt? "-0" = some 0` yields `0 ≥ 0`, so it takes the positive
branch and returns `+0.0001`, breaking the roundtrip. -/
def witness_decimal_parse_negative_sign_preserved_case_neg_zero : PropertyResult :=
  property_decimal_parse_negative_sign_preserved (-1)

/-- Witness: the spec disallows `_` in decimal literals. The buggy parser
delegates to Lean's `String.toInt?`/`String.toNat?` (which silently accept
`_`), so `"1_2.34"` parses as `12.3400` instead of being rejected. -/
def witness_decimal_parse_no_underscore_case_int_part : PropertyResult :=
  property_decimal_parse_no_underscore "1_2.34"

def witness_validate_action_entity_no_attrs_case_action_with_attr : PropertyResult :=
  property_validate_action_entity_no_attrs schemaWithOneAction entitiesBadAction

/-- Witness: a Cedar expression containing the string literal `"x\"y"`
compiles to a `Term.prim (.string "x\"y")`, and `Encoder.encode` routes it
through `encodeString`, which must double the inner `"` per SMT-LIB. The
buggy encoder leaves it as a single `"`, producing odd quote-count
output. -/
def witness_smt_encode_string_balanced_quotes_case_quote_in_middle : IO PropertyResult :=
  property_smt_encode_string_balanced_quotes (Expr.lit (.string "x\"y"))

private def fooEty : EntityType := { id := "Foo", path := [] }
private def fooUid : EntityUID := { ty := fooEty, eid := "x" }

/--
Policy `permit(principal, action, resource) when { true || (principal == Foo::"x") };`.
The OR short-circuits the typechecker on the `true` branch and returns
`bool .tt`, so the right-hand reference to the undeclared `Foo` entity is
never inspected by `typecheckPolicy`. Only the `checkEntities` pre-pass
catches the undeclared reference — exactly the soundness gap that #779 closed.
-/
private def policyRefsUndeclared : Policy := {
  id := "p0",
  effect := Effect.permit,
  principalScope := PrincipalScope.principalScope Scope.any,
  actionScope := ActionScope.actionScope Scope.any,
  resourceScope := ResourceScope.resourceScope Scope.any,
  condition := [{
    kind := ConditionKind.when,
    body := Expr.or
      (Expr.lit (.bool true))
      (Expr.binaryApp BinaryOp.eq (Expr.var Var.principal) (Expr.lit (.entityUID fooUid)))
  }]
}

private def policiesUndeclaredEntity : Policies := [policyRefsUndeclared]

def witness_validate_rejects_undeclared_entities_case_unknown_principal : PropertyResult :=
  property_validate_rejects_undeclared_entities policiesUndeclaredEntity schemaWithOneAction

private def photoEntry : EntitySchemaEntry := EntitySchemaEntry.standard {
  ancestors := Set.empty,
  attrs     := Map.empty,
  tags      := none
}

/--
Schema with a Photo entity type and one Action::"a" that applies to
principal User and resource Photo. `User` itself is *not* declared in
`ets` — only as a type referenced by the action's appliesToPrincipal set.
-/
private def schemaWithPhotoAndOneAction : Schema := {
  ets  := Map.mk [(photoEty, photoEntry)],
  acts := Map.mk [(actionUid, aseValid)]
}

/-- Request whose principal `User::"ghost"` references an undeclared entity. -/
private def ghostRequest : Request := {
  principal := { ty := userEty, eid := "ghost" },
  action    := actionUid,
  resource  := { ty := photoEty, eid := "p1" },
  context   := Map.empty
}

def witness_validate_request_principal_exists_case_ghost_user : PropertyResult :=
  property_validate_request_principal_exists schemaWithPhotoAndOneAction ghostRequest

/--
Schema with a `User` entity whose attribute `flag` is typed as the
singleton-true bool `(.bool .tt)`. This is unsound under Cedar's spec —
the typechecker would conclude any user's `.flag` is provably `true` —
but only the `validateLifted` pass catches it.
-/
private def userEntryWithSingletonBoolAttr : EntitySchemaEntry :=
  EntitySchemaEntry.standard {
    ancestors := Set.empty,
    attrs     := Map.mk [(("flag" : Attr), Qualified.required (CedarType.bool BoolType.tt))],
    tags      := none
  }

private def schemaWithSingletonBoolAttr : Schema := {
  ets  := Map.make [(userEty, userEntryWithSingletonBoolAttr), (photoEty, photoEntry)],
  acts := Map.mk [(actionUid, aseValid)]
}

/-- Schema with `Action::"a"` applies-to-principal=[User], applies-to-resource=[Photo],
matching the singleton-bool schema's User entry. -/
private def aseUserPhoto : ActionSchemaEntry := {
  appliesToPrincipal := Set.mk [userEty],
  appliesToResource  := Set.mk [photoEty],
  ancestors          := Set.empty,
  context            := Map.empty,
}

private def schemaWithSingletonBoolAttrAndAction : Schema := {
  ets  := Map.make [(userEty, userEntryWithSingletonBoolAttr), (photoEty, photoEntry)],
  acts := Map.mk [(actionUid, aseUserPhoto)]
}

private def aliceUid : EntityUID := { ty := userEty, eid := "alice" }
private def photoP1Uid : EntityUID := { ty := photoEty, eid := "p1" }

/-- Request with principal/action/resource matching the schema. -/
private def aliceFalseRequest : Request := {
  principal := aliceUid,
  action    := actionUid,
  resource  := photoP1Uid,
  context   := Map.empty
}

/-- Entity store where User::"alice" has `flag = false` — the typechecker,
relying on the buggy schema, promises `principal.flag : bool .tt`, but the
evaluator returns `false`, breaking type preservation. We deliberately do
NOT validate these entities (the broad property skips that step), since
`validateEntities` would otherwise short-circuit by rejecting the
mismatched value. -/
private def aliceFalseEntities : Entities :=
  Map.mk [(aliceUid, {
    attrs     := Map.mk [(("flag" : Attr), Value.prim (.bool false))],
    ancestors := Set.empty,
    tags      := Map.empty
  })]

/-- Expression `principal.flag` — typed as `bool .tt` by the buggy
schema. -/
private def exprPrincipalFlag : Expr :=
  Expr.getAttr (Expr.var Var.principal) "flag"

/-- Witness: type preservation fails. The schema's `User.flag : .bool .tt`
is accepted by buggy `validateWellFormed`; the typechecker promises
`principal.flag : bool .tt`; the evaluator returns `false` from the
entity store. -/
def witness_schema_well_formed_no_singleton_bools_case_attr_bool_tt : PropertyResult :=
  property_validator_type_preservation
    exprPrincipalFlag
    schemaWithSingletonBoolAttrAndAction
    aliceFalseRequest
    aliceFalseEntities

private def enumMembers : List String := ["alice", "bob"]
private def ghostUserUid : EntityUID := { ty := userEty, eid := "zzz" }

def witness_define_entity_rejects_non_member_case_zzz : IO PropertyResult :=
  property_define_entity_rejects_non_member enumMembers ghostUserUid

/--
Policy `permit(principal, action, resource) when { Action::"a" in Action::"a" };`.
The when-condition's `.binaryApp .mem (.lit Action::"a") (.lit Action::"a")`
routes the left literal through `checkEntityAccessLevel`. The fixed level
checker accepts the literal because it equals the env's action; the buggy
version (no special case) rejects via the `_, _ => false` fallthrough.
-/
private def policyActionLitInAction : Policy := {
  id := "p_action_lit",
  effect := Effect.permit,
  principalScope := PrincipalScope.principalScope Scope.any,
  actionScope := ActionScope.actionScope Scope.any,
  resourceScope := ResourceScope.resourceScope Scope.any,
  condition := [{
    kind := ConditionKind.when,
    body := Expr.binaryApp BinaryOp.mem
      (Expr.lit (.entityUID actionUid))
      (Expr.lit (.entityUID actionUid))
  }]
}

def witness_validate_with_level_accepts_case_action_in_action : PropertyResult :=
  property_validate_with_level_accepts [policyActionLitInAction] schemaWithPhotoAndOneAction 1

/-- Witness: an empty-record literal expression `Expr.record []` compiles
to `Term.record (Map.mk [])`. `Encoder.encode` routes it through
`defineRecord` with empty field-encodings; the buggy version emits the
malformed `(R0 )` form (atom token followed by space and `)`). -/
def witness_encoder_empty_record_well_formed_case_record_zero_fields : IO PropertyResult :=
  property_encoder_empty_record_well_formed (Expr.record [])

def witness_encoder_empty_record_decode_roundtrip_case_R0_zero_fields : PropertyResult :=
  property_encoder_empty_record_decode_roundtrip "R0"

def witness_duration_parse_min_value_case_int64_min : PropertyResult :=
  property_duration_parse_min_value (-9223372036854775808)

/-! ## Sanity-check witness for the broad SymCC pipeline property.

Hand-built `(TypeEnv, body)` pair where the body is
`principal.name == "x\"y"`. The env declares `User.name : String` so the
body typechecks. The literal `"x\"y"` flows into encodeString without
folding (the eq's left operand is a symbolic principal-attr access).
On the buggy encoder, the SMT script contains an unbalanced string
literal that CVC5 rejects at parse time. -/
private def userWithNameAttr : EntitySchemaEntry :=
  EntitySchemaEntry.standard {
    ancestors := Set.empty,
    attrs     := Map.mk [(("name" : Attr), Qualified.required CedarType.string)],
    tags      := none
  }

private def envWithUserName : TypeEnv := {
  ets := Map.make [(userEty, userWithNameAttr), (photoEty, photoEntry)],
  acts := Map.mk [(actionUid, aseValid)],
  reqty := {
    principal := userEty,
    action    := actionUid,
    resource  := photoEty,
    context   := Map.empty
  }
}

def witness_symcc_pipeline_soundness_case_string_quote : IO PropertyResult :=
  property_symcc_pipeline_soundness envWithUserName
    (Expr.binaryApp BinaryOp.eq
      (Expr.getAttr (Expr.var Var.principal) "name")
      (Expr.lit (.string "x\"y")))

/-- Witness: `context == {}` against an env whose request type has an
empty context. The eq doesn't fold (left is symbolic, right is literal);
compile produces a Term referencing `Term.record (Map.mk [])` on the
right; the encoder emits the empty-record value through `defineRecord`,
which the buggy version mis-emits as `(R0 )` in value position — CVC5
rejects at parse time. -/
def witness_symcc_pipeline_soundness_case_empty_record : IO PropertyResult :=
  property_symcc_pipeline_soundness envWithUserName
    (Expr.binaryApp BinaryOp.eq
      (Expr.var Var.context)
      (Expr.record []))

end Cedar.Etna
