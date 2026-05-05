/-
Type-directed Cedar `Expr` generation.

A blackbox PBT property over Cedar's typechecker → SymCC → solver →
decoder pipeline needs randomly-generated `(TypeEnv, Expr, Request,
Entities)` quadruples that are jointly well-typed: the `Expr` must
typecheck against the env, the request must conform to the env's
`reqty`, and the entities must conform to the schema. A purely random
`Expr` walk has near-100% discard rate because most candidates fail
typecheck; we instead generate by *target type*.

This file mirrors the type-directed pattern used by the Rust
`cedar-policy-generators` crate (alpha-quality, not a full port — covers
the operator subset that exercises our SymCC encoder/decoder variants
plus enough type-system shape to make random generation interesting).
-/

module

public meta import Plausible
public meta import Cedar.Spec
public meta import Cedar.Validation.RequestEntityValidator
public meta import Cedar.Validation.Validator
public meta import Cedar.Etna.Generators

public meta section

namespace Cedar.Etna.TypeDirected

open Plausible
open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/-! ## Helpers — query the TypeEnv for what's reachable. -/

/-- All `(EntityType, Attr)` pairs in the env where the attr's type is `target`. -/
public def attrsOfType (env : TypeEnv) (target : CedarType) : List (EntityType × Attr) :=
  env.ets.toList.flatMap (fun (ety, entry) =>
    match entry with
    | .standard se =>
      se.attrs.toList.filterMap (fun (a, qt) =>
        if qt.getType == target then some (ety, a) else none)
    | .enum _ => [])

/-- All entity types declared in the env that have at least one attr of `target` type. -/
public def entityTypesWithAttr (env : TypeEnv) (target : CedarType) : List EntityType :=
  (attrsOfType env target).map Prod.fst |>.eraseDups

/-- All attrs of `target` type on a given entity type. -/
public def attrsOnEntityType (env : TypeEnv) (ety : EntityType) (target : CedarType) : List Attr :=
  match env.ets.find? ety with
  | some (.standard se) =>
    se.attrs.toList.filterMap (fun (a, qt) =>
      if qt.getType == target then some a else none)
  | _ => []

/-- All `Var`s whose type-under-env equals `target`. -/
public def varsOfType (env : TypeEnv) (target : CedarType) : List Var :=
  let candidates : List (Var × CedarType) := [
    (.principal, .entity env.reqty.principal),
    (.resource,  .entity env.reqty.resource),
    (.context,   .record env.reqty.context),
  ]
  candidates.filterMap (fun (v, vty) => if vty == target then some v else none)

/-! ## Random small-string generation for spec-relevant inputs. -/

/-- Random short ASCII string biased toward including special characters
that exercise encoder paths (`"`, `\\`, `_`). -/
public def genTrickyString : Gen String := do
  let n ← Gen.choose Nat 0 6 (Nat.zero_le _)
  let cs ← (List.range n.val).mapM (fun _ => do
    let i ← Gen.choose Nat 0 12 (Nat.zero_le _)
    return match i.val with
    | 0 => '"'
    | 1 => '\\'
    | 2 => '_'
    | k => Char.ofNat (Nat.min 126 (32 + k * 7))) -- spread across printable ASCII
  return String.ofList cs

/-! ## TypeEnv generation — small but interesting. -/

/-- Pool of attr names for generated schemas. Small so collision rates are
useful — we want generated Exprs to actually reference real attrs. -/
private def stdAttrs : List String := ["name", "owner", "flag", "count", "tags", "meta"]

private def genQualifiedSimple : Gen (Qualified CedarType) := do
  let isReq ← Gen.chooseAny Bool
  let bty ← Gen.frequency (pure .int) [
    (3, pure .int),
    (3, pure .string),
    (3, pure (.bool .anyBool)),
    (1, pure (.record (Map.mk []))), -- empty record — exercises variant 5/6
  ]
  return if isReq then .required bty else .optional bty

private def genStandardEntry : Gen StandardSchemaEntry := do
  let nAttrs ← Gen.choose Nat 0 3 (Nat.zero_le _)
  let usedNames ← (List.range nAttrs.val).mapM (fun _ => Cedar.Etna.gen stdAttrs)
  let attrs : List (Attr × Qualified CedarType) ←
    usedNames.eraseDups.mapM (fun a => do
      let qt ← genQualifiedSimple
      return (a, qt))
  return { ancestors := Set.empty, attrs := Map.make attrs, tags := none }

/-- Generate a small TypeEnv: 1-2 entity types, 1 action, well-formed
applies-to. Returns `none` when the random pick produced an inconsistent
combination (caller should retry or fall back). -/
public def genTypeEnv : Gen TypeEnv := do
  let principalEty : EntityType := { id := "User", path := [] }
  let resourceEty  : EntityType := { id := "Photo", path := [] }
  let actionEty    : EntityType := { id := "Action", path := [] }
  let actionUid    : EntityUID  := { ty := actionEty, eid := "view" }
  let principalEntry ← genStandardEntry
  let resourceEntry  ← genStandardEntry
  let ets : EntitySchema := Map.make [
    (principalEty, .standard principalEntry),
    (resourceEty,  .standard resourceEntry),
  ]
  let nCtxAttrs ← Gen.choose Nat 0 2 (Nat.zero_le _)
  let ctxAttrNames ← (List.range nCtxAttrs.val).mapM (fun _ => Cedar.Etna.gen stdAttrs)
  let ctxAttrs : List (Attr × Qualified CedarType) ←
    ctxAttrNames.eraseDups.mapM (fun a => do
      let qt ← genQualifiedSimple
      return (a, qt))
  let ase : ActionSchemaEntry := {
    appliesToPrincipal := Set.mk [principalEty],
    appliesToResource  := Set.mk [resourceEty],
    ancestors          := Set.empty,
    context            := Map.make ctxAttrs,
  }
  let acts : ActionSchema := Map.mk [(actionUid, ase)]
  return {
    ets,
    acts,
    reqty := {
      principal := principalEty,
      action    := actionUid,
      resource  := resourceEty,
      context   := Map.make ctxAttrs,
    }
  }

/-! ## Type-directed Expr generation.

`genExprOfType env τ depth` returns an Expr that compiles to type τ
against env. Mutually recursive over the type structure. -/

private partial def genIntLit : Gen Expr := do
  let n ← Gen.choose Int (-3) 5 (by decide)
  return .lit (.int (Int64.ofInt n.val))

private partial def genStringLit : Gen Expr := do
  let s ← genTrickyString
  return .lit (.string s)

private partial def genBoolLit : Gen Expr := do
  let b ← Gen.chooseAny Bool
  return .lit (.bool b)

private partial def genEntityLit (ety : EntityType) : Gen Expr := do
  let eid ← Cedar.Etna.gen ["alice", "bob", "p1", "p2"]
  return .lit (.entityUID { ty := ety, eid })

mutual
  /-- Generate an Expr whose compile-result type is `τ` against `env`. -/
  public partial def genExprOfType (env : TypeEnv) (τ : CedarType) : Nat → Gen Expr
    | 0 => genBaseOfType env τ
    | depth + 1 => do
      -- 60% leaf, 40% recursive constructions; bias keeps things small.
      let leafChance ← Gen.choose Nat 0 9 (Nat.zero_le _)
      if leafChance.val ≤ 5 then
        genBaseOfType env τ
      else
        match τ with
        | .bool _   => genBoolCompound env depth
        | .string   => genStringCompound env depth
        | .int      => genBaseOfType env τ -- arithmetic ops are restricted; stick to leaves
        | .entity _ => genBaseOfType env τ
        | .ext _    => genBaseOfType env τ
        | .set _    => genBaseOfType env τ -- not exercising set bugs here
        | .record rty => genRecordCompound env rty depth

  /-- Leaf-or-shallow generator. -/
  private partial def genBaseOfType (env : TypeEnv) (τ : CedarType) : Gen Expr :=
    match τ with
    | .bool _   => Gen.frequency genBoolLit [
        (2, genBoolLit),
        (2, genVarOfType env τ),
        (2, genHasAttrOfBoolType env),
      ]
    | .int      => Gen.frequency genIntLit [
        (2, genIntLit),
        (2, genGetAttrOfType env .int),
      ]
    | .string   => Gen.frequency genStringLit [
        (2, genStringLit),
        (2, genGetAttrOfType env .string),
      ]
    | .entity ety => Gen.frequency (genEntityLit ety) [
        (2, genEntityLit ety),
        (2, genVarOfType env (.entity ety)),
      ]
    | .record rty =>
      -- For records: prefer var-of-record-type (gives symbolic value),
      -- but always-fall-back to a literal of the declared shape if no var
      -- has the right type. The empty-record literal is the variant-6
      -- trigger and is preserved as a leaf when rty is empty.
      if rty.toList.isEmpty then
        Gen.frequency (pure (.record [])) [
          (3, pure (.record [])),
          (2, genVarOfType env (.record rty)),
        ]
      else
        Gen.frequency (genVarOfType env (.record rty)) [
          (2, genVarOfType env (.record rty)),
          (1, do
            let fields : List (Attr × Expr) ← rty.toList.mapM (fun (a, qt) => do
              let v ← genVarOfType env qt.getType
              return (a, v))
            pure (.record fields)),
        ]
    | _ => genVarOfType env τ

  /-- Pick a `Var` of the right type, or fall back to a type-correct
  literal. Every fallback path must return an Expr of type `τ`; ill-typed
  fallbacks would inflate the discard rate during random testing. -/
  private partial def genVarOfType (env : TypeEnv) (τ : CedarType) : Gen Expr := do
    match varsOfType env τ with
    | [] =>
      match τ with
      | .bool _    => genBoolLit
      | .int       => genIntLit
      | .string    => genStringLit
      | .entity ety => genEntityLit ety  -- typecheck OK iff ety ∈ env.ets ∪ env.acts
      | .record rty =>
        -- Build a record literal of the declared shape recursively.
        let fields : List (Attr × Expr) ← rty.toList.mapM (fun (a, qt) => do
          let v ← genVarOfType env qt.getType
          return (a, v))
        pure (.record fields)
      | _          => genBoolLit
    | vs =>
      let i ← Gen.choose Nat 0 (vs.length - 1) (Nat.zero_le _)
      return .var vs[i.val]!

  /-- `principal.attr` for some principal-attr of the right type. -/
  private partial def genGetAttrOfType (env : TypeEnv) (τ : CedarType) : Gen Expr := do
    match attrsOfType env τ with
    | [] =>
      match τ with
      | .int    => genIntLit
      | .string => genStringLit
      | _       => genBoolLit
    | candidates =>
      let i ← Gen.choose Nat 0 (candidates.length - 1) (Nat.zero_le _)
      let (ety, a) := candidates[i.val]!
      let entityE ← genVarOfType env (.entity ety)
      return .getAttr entityE a

  /-- `e has attr` for some `e : entity` and attr declared on its type. -/
  private partial def genHasAttrOfBoolType (env : TypeEnv) : Gen Expr := do
    let etys := env.ets.toList.map Prod.fst
    match etys with
    | [] => genBoolLit
    | _ :: _ =>
      let i ← Gen.choose Nat 0 (etys.length - 1) (Nat.zero_le _)
      let ety := etys[i.val]!
      let attrs := match env.ets.find? ety with
        | some (.standard se) => se.attrs.toList.map Prod.fst
        | _ => ([] : List Attr)
      match attrs with
      | [] => genBoolLit
      | _ :: _ =>
        let j ← Gen.choose Nat 0 (attrs.length - 1) (Nat.zero_le _)
        let entityE ← genVarOfType env (.entity ety)
        return .hasAttr entityE attrs[j.val]!

  /-- Boolean compounds: equality, conjunction, disjunction, negation. -/
  private partial def genBoolCompound (env : TypeEnv) (depth : Nat) : Gen Expr := do
    Gen.frequency (genBoolLit) [
      (3, do
        let l ← genExprOfType env (.bool .anyBool) depth
        let r ← genExprOfType env (.bool .anyBool) depth
        return .and l r),
      (3, do
        let l ← genExprOfType env (.bool .anyBool) depth
        let r ← genExprOfType env (.bool .anyBool) depth
        return .or l r),
      (3, do
        -- Equality of two same-type sub-exprs. Pick a comparable type.
        let cTy ← Gen.frequency (pure .int) [
          (3, pure .string),
          (3, pure .int),
          (3, pure (.entity env.reqty.principal)),
          (1, pure (.record (Map.mk []))),
        ]
        let l ← genExprOfType env cTy depth
        let r ← genExprOfType env cTy depth
        return .binaryApp .eq l r),
      (2, genHasAttrOfBoolType env),
    ]

  /-- String compounds — currently just literals + getAttr (no concat). -/
  private partial def genStringCompound (env : TypeEnv) (_ : Nat) : Gen Expr :=
    Gen.frequency genStringLit [
      (2, genStringLit),
      (3, genGetAttrOfType env .string),
    ]

  /-- Record compounds — literal of declared shape, or var/attr access. -/
  private partial def genRecordCompound (env : TypeEnv) (rty : RecordType) (depth : Nat) : Gen Expr := do
    if rty.toList.isEmpty then
      Gen.frequency (pure (.record [])) [
        (5, pure (.record [])),
        (1, genVarOfType env (.record rty)),
      ]
    else
      -- Build a record literal matching the declared shape.
      let fields : List (Attr × Expr) ← rty.toList.mapM (fun (a, qt) => do
        let v ← genExprOfType env qt.getType depth
        return (a, v))
      return .record fields
end

/-- Top-level: a Bool-typed Expr suitable as a policy body. -/
public def genPolicyBody (env : TypeEnv) (depth : Nat := 3) : Gen Expr :=
  genExprOfType env (.bool .anyBool) depth

/-! ## Joint generators. -/

/-- A `Request` matching the env's `reqty`. -/
public def genRequestForEnv (env : TypeEnv) : Gen Request := do
  let pEid ← Cedar.Etna.gen ["alice", "bob"]
  let rEid ← Cedar.Etna.gen ["p1", "p2"]
  let ctxFields : List (Attr × Value) ← env.reqty.context.toList.mapM (fun (a, qt) => do
    let v : Value ← match qt.getType with
      | .int    => pure (.prim (.int (Int64.ofInt 0)))
      | .string => pure (.prim (.string ""))
      | .bool _ => pure (.prim (.bool false))
      | _      => pure (.record (Map.mk []))
    return (a, v))
  return {
    principal := { ty := env.reqty.principal, eid := pEid },
    action    := env.reqty.action,
    resource  := { ty := env.reqty.resource, eid := rEid },
    context   := Map.make ctxFields,
  }

/-- Default value matching a `CedarType`, used when populating entities. -/
private partial def defaultValueOf : CedarType → Value
  | .bool _    => .prim (.bool false)
  | .int       => .prim (.int (Int64.ofInt 0))
  | .string    => .prim (.string "")
  | .entity ety => .prim (.entityUID { ty := ety, eid := "" })
  | .set _     => .set Set.empty
  | .record _  => .record (Map.mk [])
  | .ext _     => .prim (.bool false) -- placeholder; no ext gen here

/-- Generate `Entities` consistent with `env`. Each declared entity type
gets one or two instances with default-value attrs. -/
public def genEntitiesForEnv (env : TypeEnv) : Gen Entities := do
  let entries : List (EntityUID × EntityData) ← env.ets.toList.flatMapM (fun (ety, entry) => do
    match entry with
    | .standard se =>
      let attrFields : List (Attr × Value) := se.attrs.toList.map (fun (a, qt) =>
        (a, defaultValueOf qt.getType))
      let eids := ["alice", "bob", "p1", "p2"]
      return eids.map (fun eid =>
        ({ ty := ety, eid }, {
          attrs     := Map.make attrFields,
          ancestors := Set.empty,
          tags      := Map.empty,
        }))
    | .enum _ => return [])
  return Map.make entries

/-- Joint generator for the full input quadruple consumed by the broad
type-preservation property. -/
public def genJointInputs : Gen (TypeEnv × Expr × Request × Entities) := do
  let env ← genTypeEnv
  let expr ← genPolicyBody env 3
  let request ← genRequestForEnv env
  let entities ← genEntitiesForEnv env
  return (env, expr, request, entities)

end Cedar.Etna.TypeDirected

end
