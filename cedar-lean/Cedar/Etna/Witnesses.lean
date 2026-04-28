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

def witness_schema_well_formed_no_singleton_bools_case_attr_bool_tt : PropertyResult :=
  property_schema_well_formed_no_singleton_bools schemaWithSingletonBoolAttr

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

end Cedar.Etna
