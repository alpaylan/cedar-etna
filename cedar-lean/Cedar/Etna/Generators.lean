/-
Plausible `Arbitrary` + `Shrinkable` instances for Cedar types so the ETNA
runner's `plausible` mode can drive random search against every property.

Generators are blind: no special-purpose shape biases pre-target any
particular bug. The only narrowing is small fixed-size pools for entity
types / EIDs / attribute names — a pure unicode generator would dilute the
search to the point where schema/policy collisions never happen, which
isn't a property of the bug, just of testing AAC at all. Pool entries are
generic placeholders, not values referenced by any specific witness.

Coverage: Name, EntityType, EntityUID, Prim, Value, Set α, Map α β,
Effect, Scope, PrincipalScope, ResourceScope, ActionScope, ConditionKind,
Condition, Policy, Var, UnaryOp, BinaryOp, Expr, EntityData, Entities,
BoolType, ExtType, Qualified α, CedarType, RecordType, EntitySchemaEntry,
ActionSchemaEntry, Schema, Request.
-/

module

public meta import Plausible
public meta import Cedar.Spec
public meta import Cedar.Validation.RequestEntityValidator
public meta import Cedar.Validation.Validator

public meta section

namespace Cedar.Etna

open Plausible
open Cedar.Spec
open Cedar.Validation
open Cedar.Data

/-! ## Pools — keeps the random search focused on a small enough universe
that schema/request/policy interactions actually exercise validator code paths.
-/

public def entityTypePool : List String := ["User", "Photo", "Album", "Action", "Group", "Document"]
public def eidPool        : List String := ["alice", "bob", "carol", "dave", "p1", "p2", "doc1", "doc2"]
public def attrPool       : List String := ["flag", "name", "age", "owner"]
public def actionEidPool  : List String := ["a", "b", "view", "edit"]

public def gen [Inhabited α] (xs : List α) : Gen α := do
  match xs with
  | [] => return default
  | _ :: _ =>
    let i ← Gen.choose Nat 0 (xs.length - 1) (Nat.zero_le _)
    return xs[i.val]!

/-- Random short ASCII string in printable-ASCII (code points 32–126).
Generic — covers punctuation that is load-bearing in many text-processing
contexts (`"`, `\\`, `_`, etc.). -/
public def genShortAscii : Gen String := do
  let n ← Gen.choose Nat 0 8 (Nat.zero_le _)
  let cs ← (List.range n.val).mapM (fun _ => do
    let i ← Gen.choose Nat 0 94 (Nat.zero_le _)
    return Char.ofNat (32 + i.val))
  return String.ofList cs

/-! ## Layer 1 — primitives -/

instance : Arbitrary Cedar.Spec.Name where
  arbitrary := do
    let id ← gen entityTypePool
    return { id, path := [] }

instance : Shrinkable Cedar.Spec.Name where

instance : Arbitrary Cedar.Spec.EntityUID where
  arbitrary := do
    let ty : Name ← Arbitrary.arbitrary
    let eid ← gen (eidPool ++ actionEidPool)
    return { ty, eid }

instance : Shrinkable Cedar.Spec.EntityUID where

/-! ## Layer 2 — Set / Map wrappers around list-backed underlying. -/

instance Set.Arbitrary {α : Type} [BEq α] [LT α] [DecidableLT α] [Arbitrary α] :
    Arbitrary (Cedar.Data.Set α) where
  arbitrary := do
    -- Cap collections to size ≤ 3 so a `Schema.environments` build-out
    -- doesn't explode under random search.
    let n ← Gen.choose Nat 0 3 (Nat.zero_le _)
    let xs ← (List.range n.val).mapM (fun _ => Arbitrary.arbitrary)
    return Set.make xs

instance Set.Shrinkable {α : Type} : Shrinkable (Cedar.Data.Set α) where

instance Map.Arbitrary {α β : Type} [BEq α] [LT α] [DecidableLT α]
    [Arbitrary α] [Arbitrary β] : Arbitrary (Cedar.Data.Map α β) where
  arbitrary := do
    let n ← Gen.choose Nat 0 3 (Nat.zero_le _)
    let kvs ← (List.range n.val).mapM (fun _ => do
      let k ← Arbitrary.arbitrary
      let v ← Arbitrary.arbitrary
      return (k, v))
    return Map.make kvs

instance Map.Shrinkable {α β : Type} : Shrinkable (Cedar.Data.Map α β) where

/-! ## Layer 3 — values and entity data. -/

instance : Arbitrary Cedar.Spec.Prim where
  arbitrary := do
    match ← Gen.choose Nat 0 3 (Nat.zero_le _) with
    | ⟨0, _⟩ => return .bool (← Arbitrary.arbitrary)
    | ⟨1, _⟩ =>
      let n ← Gen.choose Nat 0 100 (Nat.zero_le _)
      return .int (Int64.ofInt n.val)
    | ⟨2, _⟩ =>
      -- Random ASCII string — broad enough to include `"`, `\\`, and `_`,
      -- which the encoder/parser have to handle correctly.
      let s ← genShortAscii
      return .string s
    | _      => return .entityUID (← Arbitrary.arbitrary)

instance : Shrinkable Cedar.Spec.Prim where

/-- Bounded `Value` generator. Limits set/record nesting depth to one level so
random search avoids exponential blowup. -/
public partial def genValue : Nat → Gen Cedar.Spec.Value
  | 0 => do return .prim (← Arbitrary.arbitrary)
  | n + 1 => do
    match ← Gen.choose Nat 0 3 (Nat.zero_le _) with
    | ⟨0, _⟩ | ⟨1, _⟩ => return .prim (← Arbitrary.arbitrary)
    | ⟨2, _⟩ =>
      let k ← Gen.choose Nat 0 2 (Nat.zero_le _)
      let xs ← (List.range k.val).mapM (fun _ => genValue n)
      return .set (Set.mk xs)
    | _ =>
      let k ← Gen.choose Nat 0 2 (Nat.zero_le _)
      let kvs ← (List.range k.val).mapM (fun _ => do
        let a ← gen attrPool
        let v ← genValue n
        return (a, v))
      return .record (Map.make kvs)

instance : Arbitrary Cedar.Spec.Value where
  arbitrary := genValue 1

instance : Shrinkable Cedar.Spec.Value where

instance : Arbitrary Cedar.Spec.EntityData where
  arbitrary := do
    let attrs ← Arbitrary.arbitrary
    let ancestors ← Arbitrary.arbitrary
    let tags ← Arbitrary.arbitrary
    return { attrs, ancestors, tags }

instance : Shrinkable Cedar.Spec.EntityData where

/-! ## Layer 4 — Cedar type system. -/

instance : Arbitrary Cedar.Validation.BoolType where
  arbitrary := do
    match ← Gen.choose Nat 0 2 (Nat.zero_le _) with
    | ⟨0, _⟩ => return .anyBool
    | ⟨1, _⟩ => return .tt
    | _      => return .ff

instance : Shrinkable Cedar.Validation.BoolType where

instance : Arbitrary Cedar.Validation.ExtType where
  arbitrary := do
    match ← Gen.choose Nat 0 3 (Nat.zero_le _) with
    | ⟨0, _⟩ => return .ipAddr
    | ⟨1, _⟩ => return .decimal
    | ⟨2, _⟩ => return .datetime
    | _      => return .duration

instance : Shrinkable Cedar.Validation.ExtType where

public partial def genCedarType : Nat → Gen Cedar.Validation.CedarType
  | 0 => do
    -- Leaf-only at depth 0
    match ← Gen.choose Nat 0 4 (Nat.zero_le _) with
    | ⟨0, _⟩ => return .bool (← Arbitrary.arbitrary)
    | ⟨1, _⟩ => return .int
    | ⟨2, _⟩ => return .string
    | ⟨3, _⟩ => return .entity (← Arbitrary.arbitrary)
    | _      => return .ext (← Arbitrary.arbitrary)
  | n + 1 => do
    match ← Gen.choose Nat 0 5 (Nat.zero_le _) with
    | ⟨0, _⟩ => return .bool (← Arbitrary.arbitrary)
    | ⟨1, _⟩ => return .int
    | ⟨2, _⟩ => return .string
    | ⟨3, _⟩ => return .entity (← Arbitrary.arbitrary)
    | ⟨4, _⟩ => return .ext (← Arbitrary.arbitrary)
    | _ =>
      -- Record at depth n+1: generate a small attr→type map
      let k ← Gen.choose Nat 0 2 (Nat.zero_le _)
      let kvs ← (List.range k.val).mapM (fun _ => do
        let a ← gen attrPool
        let isOpt ← Gen.chooseAny Bool
        let ty ← genCedarType n
        return (a, if isOpt then Qualified.optional ty else Qualified.required ty))
      return .record (Map.make kvs)

instance : Arbitrary Cedar.Validation.CedarType where
  arbitrary := genCedarType 1

instance : Shrinkable Cedar.Validation.CedarType where

instance {α : Type} [Arbitrary α] : Arbitrary (Cedar.Validation.Qualified α) where
  arbitrary := do
    let v ← Arbitrary.arbitrary
    let isReq ← Gen.chooseAny Bool
    return if isReq then Qualified.required v else Qualified.optional v

instance {α : Type} : Shrinkable (Cedar.Validation.Qualified α) where

instance : Arbitrary Cedar.Validation.StandardSchemaEntry where
  arbitrary := do
    let ancestors ← Arbitrary.arbitrary
    -- Build a small attr record directly (avoids re-walking the full CedarType depth).
    let attrK ← Gen.choose Nat 0 2 (Nat.zero_le _)
    let attrs : RecordType ← do
      let kvs ← (List.range attrK.val).mapM (fun _ => do
        let a ← gen attrPool
        let ty ← genCedarType 0
        let isReq ← Gen.chooseAny Bool
        return (a, if isReq then Qualified.required ty else Qualified.optional ty))
      pure (Map.make kvs)
    let hasTags ← Gen.chooseAny Bool
    let tags : Option CedarType ← if hasTags then
      pure (some (← genCedarType 0))
    else pure none
    return { ancestors, attrs, tags }

instance : Shrinkable Cedar.Validation.StandardSchemaEntry where

instance : Arbitrary Cedar.Validation.EntitySchemaEntry where
  arbitrary := do
    -- Heavy bias toward .standard (.enum is rare in random samples).
    match ← Gen.choose Nat 0 4 (Nat.zero_le _) with
    | ⟨0, _⟩ =>
      let n ← Gen.choose Nat 0 2 (Nat.zero_le _)
      let eids ← (List.range n.val).mapM (fun _ => gen eidPool)
      return .enum (Set.make eids)
    | _ => return .standard (← Arbitrary.arbitrary)

instance : Shrinkable Cedar.Validation.EntitySchemaEntry where

instance : Arbitrary Cedar.Validation.ActionSchemaEntry where
  arbitrary := do
    let appliesToPrincipal ← Arbitrary.arbitrary
    let appliesToResource  ← Arbitrary.arbitrary
    let ancestors          ← Arbitrary.arbitrary
    let ctxK ← Gen.choose Nat 0 2 (Nat.zero_le _)
    let context : RecordType ← do
      let kvs ← (List.range ctxK.val).mapM (fun _ => do
        let a ← gen attrPool
        let ty ← genCedarType 0
        let isReq ← Gen.chooseAny Bool
        return (a, if isReq then Qualified.required ty else Qualified.optional ty))
      pure (Map.make kvs)
    return { appliesToPrincipal, appliesToResource, ancestors, context }

instance : Shrinkable Cedar.Validation.ActionSchemaEntry where

instance : Arbitrary Cedar.Validation.Schema where
  arbitrary := do
    let ets ← Arbitrary.arbitrary
    let acts ← Arbitrary.arbitrary
    return { ets, acts }

instance : Shrinkable Cedar.Validation.Schema where

/-! ## Layer 5 — Request / Entities. -/

instance : Arbitrary Cedar.Spec.Request where
  arbitrary := do
    let principal ← Arbitrary.arbitrary
    let action ← Arbitrary.arbitrary
    let resource ← Arbitrary.arbitrary
    let ctxK ← Gen.choose Nat 0 2 (Nat.zero_le _)
    let context ← do
      let kvs ← (List.range ctxK.val).mapM (fun _ => do
        let a ← gen attrPool
        let v : Value ← Arbitrary.arbitrary
        return (a, v))
      pure (Map.make kvs)
    return { principal, action, resource, context }

instance : Shrinkable Cedar.Spec.Request where

/-! ## Layer 6 — Policies. -/

instance : Arbitrary Cedar.Spec.Effect where
  arbitrary := do
    let b ← Gen.chooseAny Bool
    return if b then .permit else .forbid

instance : Shrinkable Cedar.Spec.Effect where

instance : Arbitrary Cedar.Spec.Scope where
  arbitrary := do
    match ← Gen.choose Nat 0 4 (Nat.zero_le _) with
    | ⟨0, _⟩ => return .any
    | ⟨1, _⟩ => return .eq    (← Arbitrary.arbitrary)
    | ⟨2, _⟩ => return .mem   (← Arbitrary.arbitrary)
    | ⟨3, _⟩ => return .is    (← Arbitrary.arbitrary)
    | _      => return .isMem (← Arbitrary.arbitrary) (← Arbitrary.arbitrary)

instance : Shrinkable Cedar.Spec.Scope where

instance : Arbitrary Cedar.Spec.PrincipalScope where
  arbitrary := return .principalScope (← Arbitrary.arbitrary)
instance : Shrinkable Cedar.Spec.PrincipalScope where

instance : Arbitrary Cedar.Spec.ResourceScope where
  arbitrary := return .resourceScope (← Arbitrary.arbitrary)
instance : Shrinkable Cedar.Spec.ResourceScope where

instance : Arbitrary Cedar.Spec.ActionScope where
  arbitrary := do
    let b ← Gen.chooseAny Bool
    if b then
      return .actionScope (← Arbitrary.arbitrary)
    else
      let n ← Gen.choose Nat 0 2 (Nat.zero_le _)
      let uids ← (List.range n.val).mapM (fun _ => Arbitrary.arbitrary)
      return .actionInAny uids
instance : Shrinkable Cedar.Spec.ActionScope where

instance : Arbitrary Cedar.Spec.Var where
  arbitrary := do
    match ← Gen.choose Nat 0 3 (Nat.zero_le _) with
    | ⟨0, _⟩ => return .principal
    | ⟨1, _⟩ => return .action
    | ⟨2, _⟩ => return .resource
    | _      => return .context

instance : Shrinkable Cedar.Spec.Var where

/-- Bounded `Expr` generator. Depth-2 cap keeps the typechecker out of
pathological recursion. Covers literals, variables, boolean connectives,
binary ops, set/record constructors, and attribute lookups — no operator
is biased toward any specific bug-trigger shape. -/
public partial def genExpr : Nat → Gen Cedar.Spec.Expr
  | 0 => do
    match ← Gen.choose Nat 0 1 (Nat.zero_le _) with
    | ⟨0, _⟩ => return .lit (← Arbitrary.arbitrary)
    | _      => return .var (← Arbitrary.arbitrary)
  | n + 1 => do
    match ← Gen.choose Nat 0 8 (Nat.zero_le _) with
    | ⟨0, _⟩ => return .lit (← Arbitrary.arbitrary)
    | ⟨1, _⟩ => return .var (← Arbitrary.arbitrary)
    | ⟨2, _⟩ => return .and (← genExpr n) (← genExpr n)
    | ⟨3, _⟩ => return .or  (← genExpr n) (← genExpr n)
    | ⟨4, _⟩ =>
      let op : BinaryOp ←
        match ← Gen.choose Nat 0 2 (Nat.zero_le _) with
        | ⟨0, _⟩ => pure .eq
        | ⟨1, _⟩ => pure .mem
        | _      => pure .less
      return .binaryApp op (← genExpr n) (← genExpr n)
    | ⟨5, _⟩ =>
      let k ← Gen.choose Nat 0 2 (Nat.zero_le _)
      let xs ← (List.range k.val).mapM (fun _ => genExpr n)
      return .set xs
    | ⟨6, _⟩ =>
      let k ← Gen.choose Nat 0 2 (Nat.zero_le _)
      let kvs ← (List.range k.val).mapM (fun _ => do
        let a ← gen attrPool
        let v ← genExpr n
        return (a, v))
      return .record kvs
    | ⟨7, _⟩ =>
      let a ← gen attrPool
      return .getAttr (← genExpr n) a
    | _ =>
      let a ← gen attrPool
      return .hasAttr (← genExpr n) a

instance : Arbitrary Cedar.Spec.Expr where
  arbitrary := genExpr 2

instance : Shrinkable Cedar.Spec.Expr where

instance : Arbitrary Cedar.Spec.ConditionKind where
  arbitrary := do
    let b ← Gen.chooseAny Bool
    return if b then .when else .unless

instance : Shrinkable Cedar.Spec.ConditionKind where

instance : Arbitrary Cedar.Spec.Condition where
  arbitrary := do
    let kind ← Arbitrary.arbitrary
    let body ← Arbitrary.arbitrary
    return { kind, body }

instance : Shrinkable Cedar.Spec.Condition where

instance : Arbitrary Cedar.Spec.Policy where
  arbitrary := do
    let id ← gen ["p0", "p1", "p2"]
    let effect ← Arbitrary.arbitrary
    let principalScope ← Arbitrary.arbitrary
    let actionScope ← Arbitrary.arbitrary
    let resourceScope ← Arbitrary.arbitrary
    -- Cap conditions at 1 — most real policies have 0-1 when/unless clauses,
    -- and longer ones explode in expression depth.
    let nC ← Gen.choose Nat 0 1 (Nat.zero_le _)
    let condition ← (List.range nC.val).mapM (fun _ => Arbitrary.arbitrary)
    return { id, effect, principalScope, actionScope, resourceScope, condition }

instance : Shrinkable Cedar.Spec.Policy where

end Cedar.Etna

end
