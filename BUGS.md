# cedar-lean — Injected Bugs

ETNA workload for the Cedar-Lean formalization (cedar-policy/cedar-spec).
Each variant reintroduces one historical bug fix by reverse-applying a patch
against a fixed base commit and pairs it with a Plausible-driven property
and a deterministic witness. Patches are the only durable per-variant artefact;
no etna/<variant> git branches are used.

Total mutations: 9

## Bug Index

| # | Variant | Name | Location | Injection | Fix Commit |
|---|---------|------|----------|-----------|------------|
| 1 | `decimal_parse_negative_sign_preserved_84fe9c6_1` | `decimal_parse_negative_sign_preserved` | `cedar-lean/Cedar/Spec/Ext/Decimal.lean:59` | `patch` | `84fe9c6d4121f6fcb6b4f032cce0ae08f23ad8d4` |
| 2 | `decimal_parse_no_underscore_a0c5812_1` | `decimal_parse_no_underscore` | `cedar-lean/Cedar/Spec/Ext/Util.lean:12` | `patch` | `a0c5812f171bcf142e43dedf8518d94becb0e11b` |
| 3 | `encoder_define_entity_rejects_non_member_fe5a046_1` | `encoder_define_entity_rejects_non_member` | `cedar-lean/Cedar/SymCC/Encoder.lean:269` | `patch` | `fe5a0464ef36716ff37ced2d7a4e62ef91a23d7e` |
| 4 | `schema_well_formed_no_singleton_bools_e785e2e_1` | `schema_well_formed_no_singleton_bools` | `cedar-lean/Cedar/Validation/EnvironmentValidator.lean:126` | `patch` | `e785e2ed37e0ec9f4c4ecb42f84f794c4735b11f` |
| 5 | `smt_encode_string_balanced_quotes_84708ca_1` | `smt_encode_string_balanced_quotes` | `cedar-lean/Cedar/SymCC/Encoder.lean:170` | `patch` | `84708ca6ab57d462306429d345b1414842330127` |
| 6 | `validate_rejects_undeclared_entities_eb3bfff_1` | `validate_rejects_undeclared_entities` | `cedar-lean/Cedar/Validation/Validator.lean:217` | `patch` | `eb3bfff4fcebff716ae86983ae78fd6407e13290` |
| 7 | `validate_request_principal_exists_1a76346_1` | `validate_request_principal_exists` | `cedar-lean/Cedar/Validation/RequestEntityValidator.lean:52` | `patch` | `1a7634653370892318d14bd9213668bf23c022de` |
| 8 | `validate_with_level_accepts_c186f0f_1` | `validate_with_level_accepts` | `cedar-lean/Cedar/Validation/Levels.lean:61` | `patch` | `c186f0f4d34c7f244836279e0b4aa6535e1ce252` |
| 9 | `validator_action_entity_no_attrs_d7ab5ab_1` | `validator_action_entity_no_attrs` | `cedar-lean/Cedar/Validation/RequestEntityValidator.lean:132` | `patch` | `d7ab5abeff0d55f23914b5f2257da8fe3e917002` |

## Property Mapping

| Variant | Property | Witness(es) |
|---------|----------|-------------|
| `decimal_parse_negative_sign_preserved_84fe9c6_1` | `DecimalParseNegativeSignPreserved` | `witness_decimal_parse_negative_sign_preserved_case_neg_zero` |
| `decimal_parse_no_underscore_a0c5812_1` | `DecimalParseNoUnderscore` | `witness_decimal_parse_no_underscore_case_int_part` |
| `encoder_define_entity_rejects_non_member_fe5a046_1` | `DefineEntityRejectsNonMember` | `witness_define_entity_rejects_non_member_case_zzz` |
| `schema_well_formed_no_singleton_bools_e785e2e_1` | `SchemaWellFormedNoSingletonBools` | `witness_schema_well_formed_no_singleton_bools_case_attr_bool_tt` |
| `smt_encode_string_balanced_quotes_84708ca_1` | `SmtEncodeStringBalancedQuotes` | `witness_smt_encode_string_balanced_quotes_case_quote_in_middle` |
| `validate_rejects_undeclared_entities_eb3bfff_1` | `ValidateRejectsUndeclaredEntities` | `witness_validate_rejects_undeclared_entities_case_unknown_principal` |
| `validate_request_principal_exists_1a76346_1` | `ValidateRequestPrincipalExists` | `witness_validate_request_principal_exists_case_ghost_user` |
| `validate_with_level_accepts_c186f0f_1` | `ValidateWithLevelAccepts` | `witness_validate_with_level_accepts_case_action_in_action` |
| `validator_action_entity_no_attrs_d7ab5ab_1` | `ValidateActionEntityNoAttrs` | `witness_validate_action_entity_no_attrs_case_action_with_attr` |

## Framework Coverage

| Property | proptest | quickcheck | crabcheck | hegel |
|----------|---------:|-----------:|----------:|------:|
| `DecimalParseNegativeSignPreserved` | ✓ | ✓ | ✓ | ✓ |
| `DecimalParseNoUnderscore` | ✓ | ✓ | ✓ | ✓ |
| `DefineEntityRejectsNonMember` | ✓ | ✓ | ✓ | ✓ |
| `SchemaWellFormedNoSingletonBools` | ✓ | ✓ | ✓ | ✓ |
| `SmtEncodeStringBalancedQuotes` | ✓ | ✓ | ✓ | ✓ |
| `ValidateRejectsUndeclaredEntities` | ✓ | ✓ | ✓ | ✓ |
| `ValidateRequestPrincipalExists` | ✓ | ✓ | ✓ | ✓ |
| `ValidateWithLevelAccepts` | ✓ | ✓ | ✓ | ✓ |
| `ValidateActionEntityNoAttrs` | ✓ | ✓ | ✓ | ✓ |

## Bug Details

### 1. decimal_parse_negative_sign_preserved

- **Variant**: `decimal_parse_negative_sign_preserved_84fe9c6_1`
- **Location**: `cedar-lean/Cedar/Spec/Ext/Decimal.lean:59` (inside `Cedar.Spec.Ext.Decimal.parse`)
- **Property**: `DecimalParseNegativeSignPreserved`
- **Witness(es)**:
  - `witness_decimal_parse_negative_sign_preserved_case_neg_zero` — minimal repro: "-0.5"
- **Source**: [#799](https://github.com/cedar-policy/cedar-spec/pull/799) — Fix parsing of decimal literals (#799)
  > Decimal.parse computed the result's sign from the parsed integer part
  > (`if l ≥ 0 then add else subtract`). For inputs like "-0.5" the integer
  > part is "-0", which `String.toInt?` returns as `0`, so the sign test
  > took the wrong branch and emitted `+0.5000` instead of `-0.5000`.
  > The fix tests the leading minus textually: `if !left.startsWith "-"`.
- **Fix commit**: `84fe9c6d4121f6fcb6b4f032cce0ae08f23ad8d4` — Fix parsing of decimal literals (#799)
- **Invariant violated**: If `Decimal.parse s = some d`, then a leading '-' in `s` must yield a non-positive `d` — i.e. textual sign is preserved through parsing.
- **How the mutation triggers**: Inferring sign from `l ≥ 0` instead of from the literal prefix `-` causes "-0.<frac>" inputs (whose integer part round-trips to 0) to be mis-signed: parse("-0.5") returns `+0.5000`.

### 2. decimal_parse_no_underscore

- **Variant**: `decimal_parse_no_underscore_a0c5812_1`
- **Location**: `cedar-lean/Cedar/Spec/Ext/Util.lean:12` (inside `Cedar.Spec.Ext.toInt?'`)
- **Property**: `DecimalParseNoUnderscore`
- **Witness(es)**:
  - `witness_decimal_parse_no_underscore_case_int_part` — minimal repro: "1_2.34"
- **Source**: [#877](https://github.com/cedar-policy/cedar-spec/pull/877) — fix behavior of Decimal.parse with underscores (#877)
  > Lean's `String.toInt?`/`String.toNat?` silently accept `_` characters
  > (`String.toInt? "1_2" = some 12`). Cedar's spec disallows underscores in
  > decimal literals; without a guard the parser leaked Lean's behavior and
  > let inputs like "1_2.34" parse to 12.3400. The fix introduced
  > `toInt?'`/`toNat?'` wrappers in `Cedar.Spec.Ext.Util` that reject any
  > input containing `_` before delegating.
- **Fix commit**: `a0c5812f171bcf142e43dedf8518d94becb0e11b` — fix behavior of Decimal.parse with underscores (#877)
- **Invariant violated**: If `Decimal.parse s = some _`, then `s` does not contain `_`.
- **How the mutation triggers**: Removing the `if str.contains '_' then .none else …` gates from `toInt?'`/`toNat?'` exposes Lean's lenient `String.toInt?` behavior to the parser, so `Decimal.parse "1_2.34"` returns `some 12.3400` instead of `none`.

### 3. encoder_define_entity_rejects_non_member

- **Variant**: `encoder_define_entity_rejects_non_member_fe5a046_1`
- **Location**: `cedar-lean/Cedar/SymCC/Encoder.lean:269` (inside `Cedar.SymCC.Encoder.defineEntity`)
- **Property**: `DefineEntityRejectsNonMember`
- **Witness(es)**:
  - `witness_define_entity_rejects_non_member_case_zzz` — User enum [alice, bob], call defineEntity for User::"zzz"; fix throws, bug returns U_enc_m2
- **Source**: [#855](https://github.com/cedar-policy/cedar-spec/pull/855) — Fix escaping for euid in term protobuf (#855)
  > SymCC encoder soundness gap. Pre-#855, `defineEntity` looked up an
  > enum member's index via `members.idxOf entity.eid` (the non-Option
  > variant). For an entity whose type has a registered enum but whose
  > `eid` is *not* a declared member, `List.idxOf` returns
  > `members.length` — an index outside the legal range. The encoder
  > then emits `{tyEnc}_m{members.length}` as the SMT identifier,
  > referencing a member that does not exist. Solvers either return
  > spurious UNSAT or accept an unsound model; either way the symbolic
  > analysis loses its meaning.
  > 
  > The fix replaced `idxOf` with `idxOf?` and explicitly threw an
  > `IO.userError` on the `none` case.
- **Fix commit**: `fe5a0464ef36716ff37ced2d7a4e62ef91a23d7e` — Fix escaping for euid in term protobuf (#855)
- **Invariant violated**: If `defineEntity tyEnc entity` returns `Ok` for an entity whose type is registered as an enum, then `entity.eid` is one of the declared members.
- **How the mutation triggers**: Replacing the inner `match members.idxOf? entity.eid with | .some idx => … | .none => throw …` with the single line `return s!"{enumId tyEnc (members.idxOf entity.eid)}"` lets `defineEntity` succeed for non-member eids: `List.idxOf` returns `members.length`, producing the bogus identifier `U_enc_m2` for `["alice", "bob"]`-membered `User::"zzz"`.

### 4. schema_well_formed_no_singleton_bools

- **Variant**: `schema_well_formed_no_singleton_bools_e785e2e_1`
- **Location**: `cedar-lean/Cedar/Validation/EnvironmentValidator.lean:126` (inside `Cedar.Validation.StandardSchemaEntry.validateWellFormed`)
- **Property**: `SchemaWellFormedNoSingletonBools`
- **Witness(es)**:
  - `witness_schema_well_formed_no_singleton_bools_case_attr_bool_tt` — schema declares User.flag : (.bool .tt) — fix rejects via validateLifted, bug accepts
- **Source**: [#689](https://github.com/cedar-policy/cedar-spec/pull/689) — Require that well-formed `TypeEnv` does not have singleton Bool types (#689)
  > TypeEnv well-formedness gap. The Cedar typechecker's soundness proofs
  > assume every schema-level type is *lifted* — i.e. boolean types appear
  > only as `.bool .anyBool`, never as the singleton `.bool .tt` or
  > `.bool .ff`. Without enforcement, a malicious schema declaring an
  > attribute as `(.bool .tt)` would pass `Schema.validateWellFormed`, then
  > the typechecker would prove the literal-specific judgement (`flag :
  > bool .tt`) about user-provided attribute data — unsound under the
  > operational semantics, since the user can put `flag = false` in their
  > entity.
  > 
  > The fix added `CedarType.validateLifted` and called it on every schema
  > entry's attribute and tag types from inside
  > `StandardSchemaEntry.validateWellFormed` and
  > `ActionSchemaEntry.validateWellFormed`.
- **Fix commit**: `e785e2ed37e0ec9f4c4ecb42f84f794c4735b11f` — Require that well-formed `TypeEnv` does not have singleton Bool types (#689)
- **Invariant violated**: If `Schema.validateWellFormed schema = .ok ()`, then for every standard entity entry in `schema.ets`, the attribute record passes `CedarType.validateLifted` (no `.bool .tt` / `.bool .ff` nested anywhere).
- **How the mutation triggers**: Removing the `(CedarType.record entry.attrs).validateLifted` line from `StandardSchemaEntry.validateWellFormed` lets the validator accept entities whose attributes have singleton-bool types. The witness builds a schema with `User.flag : (.bool .tt)` and observes `Schema.validateWellFormed` returning `.ok ()` instead of `"bool type is not lifted"`.

### 5. smt_encode_string_balanced_quotes

- **Variant**: `smt_encode_string_balanced_quotes_84708ca_1`
- **Location**: `cedar-lean/Cedar/SymCC/Encoder.lean:170` (inside `Cedar.SymCC.encodeString`)
- **Property**: `SmtEncodeStringBalancedQuotes`
- **Witness(es)**:
  - `witness_smt_encode_string_balanced_quotes_case_quote_in_middle` — input "x\"y" — fix doubles the inner quote, bug emits malformed SMT
- **Source**: [#640](https://github.com/cedar-policy/cedar-spec/pull/640) — Fix SMT encoding of string literals (#640)
  > The SMT encoder did not double `"` characters inside string literals,
  > violating the SMT-LIB 2.7 standard which prescribes `"` (a doubled quote)
  > as the only escape sequence inside a string literal. Inputs containing
  > `"` produced malformed SMT, breaking symbolic verification soundness:
  > downstream solvers either reject the query or silently misparse it.
  > 
  > The fix added the doubling rule. Cedar-lean has since refactored
  > `encodeString` to per-character encoding (also handling `\\` and
  > non-ASCII via `\u{…}`), but the doubling step at the `"` branch is
  > still load-bearing.
- **Fix commit**: `84708ca6ab57d462306429d345b1414842330127` — Fix SMT encoding of string literals (#640)
- **Invariant violated**: For any string `s`, the SMT literal `"…encodeString s…"` contains an even number of `"` characters (every literal `"` inside is doubled).
- **How the mutation triggers**: Replacing `return "\"\""` (doubled quote) with `return "\""` (single quote) in the `c = '"'` branch of `encodeString` lets a single `"` leak through; the witness `x"y` then encodes to `"x"y"` (3 `"` chars, odd) instead of `"x""y"` (4, even).

### 6. validate_rejects_undeclared_entities

- **Variant**: `validate_rejects_undeclared_entities_eb3bfff_1`
- **Location**: `cedar-lean/Cedar/Validation/Validator.lean:217` (inside `Cedar.Validation.typecheckPolicyWithEnvironments`)
- **Property**: `ValidateRejectsUndeclaredEntities`
- **Witness(es)**:
  - `witness_validate_rejects_undeclared_entities_case_unknown_principal` — policy with `true || (principal == Foo::"x")`; fix rejects undeclared Foo, bug accepts
- **Source**: [#779](https://github.com/cedar-policy/cedar-spec/pull/779) — Make lean validator check entity type and action existence before type checking (#779)
  > Validator entity-existence soundness gap. The Lean typechecker
  > short-circuits on type errors (e.g. on `true || expr`, it returns
  > `bool .tt` without descending into `expr`), so a policy referencing an
  > undeclared entity type inside a short-circuited subexpression passed
  > Lean validation while the Rust validator (which performs entity
  > existence as a separate pass) rejected it. The two validators
  > disagreed, breaking differential soundness.
  > 
  > The fix added `checkEntities`, an unconditional pre-pass at the top of
  > `typecheckPolicyWithEnvironments` that traverses each policy's `Expr`
  > and rejects any reference to an entity UID/type not declared in the
  > schema.
- **Fix commit**: `eb3bfff4fcebff716ae86983ae78fd6407e13290` — Make lean validator check entity type and action existence before type checking (#779)
- **Invariant violated**: If `validate policies schema = .ok ()`, then for every policy `p` in `policies`, `checkEntities schema p.toExpr = .ok ()` — i.e. `validate` agrees with `checkEntities` on the entity-existence question.
- **How the mutation triggers**: Removing the `(checkEntities schema policy.toExpr).mapError ...` line from `typecheckPolicyWithEnvironments` lets the typechecker short-circuit through any reference to an undeclared entity. The witness encodes `permit(principal, action, resource) when { true || (principal == Foo::"x") };` — `true || …` types as `bool .tt` without inspecting the right operand, so `validate` returns `.ok ()` despite `Foo` being absent from the schema.

### 7. validate_request_principal_exists

- **Variant**: `validate_request_principal_exists_1a76346_1`
- **Location**: `cedar-lean/Cedar/Validation/RequestEntityValidator.lean:52` (inside `Cedar.Validation.instanceOfEntityType`)
- **Property**: `ValidateRequestPrincipalExists`
- **Witness(es)**:
  - `witness_validate_request_principal_exists_case_ghost_user` — schema with Photo + Action::"a" applies-to-principal=[User], request with principal=User::"ghost"; fix rejects, bug accepts
- **Source**: [#658](https://github.com/cedar-policy/cedar-spec/pull/658) — Add `Environment.WellFormed` as a new precondition for type checking and fix relevant proofs (#658)
  > Request-validation soundness gap. Pre-#658, `instanceOfEntityType` only
  > verified that the entity's literal type matched the expected request
  > type (and, for enum types, that the eid was a valid member). Non-enum
  > entities passed regardless of whether they were declared anywhere in
  > the schema, so a 'ghost' principal like `User::"ghost"` matched a
  > request type even when `User` had no entry in `env.ets`. Downstream
  > typecheckers then assume requests are well-formed, so the soundness gap
  > silently propagates to authorization decisions.
  > 
  > The fix added `Environment.WellFormed` as a precondition and reworked
  > `instanceOfEntityType` to additionally require that the entity be
  > present in either `env.ets` or `env.acts`.
- **Fix commit**: `1a7634653370892318d14bd9213668bf23c022de` — Add `Environment.WellFormed` as a new precondition for type checking and fix relevant proofs (#658)
- **Invariant violated**: If `validateRequest schema request = .ok ()`, then `request.principal` is declared in the schema (either `schema.ets.isValidEntityUID` or `schema.acts.contains`).
- **How the mutation triggers**: Replacing the existence check `(env.ets.isValidEntityUID e || env.acts.contains e)` in `instanceOfEntityType` with `true` collapses the second conjunct, so any UID whose entity type matches the request type passes — including `User::"ghost"` against a schema that has no `User` entity declared.

### 8. validate_with_level_accepts

- **Variant**: `validate_with_level_accepts_c186f0f_1`
- **Location**: `cedar-lean/Cedar/Validation/Levels.lean:61` (inside `Cedar.Validation.TypedExpr.checkEntityAccessLevel`)
- **Property**: `ValidateWithLevelAccepts`
- **Witness(es)**:
  - `witness_validate_with_level_accepts_case_action_in_action` — policy `permit when { Action::"a" in Action::"a" }`, level=1; fix accepts, bug rejects with .levelError
- **Source**: [#573](https://github.com/cedar-policy/cedar-spec/pull/573) — Update level checking to allow access to literals equal to environment action (#573)
  > Level-checker completeness gap. Pre-#573, `TypedExpr.checkEntityAccessLevel`
  > had no case for literal entity UIDs in entity-access positions, so the
  > fallthrough `_, _ => false` rejected expressions like `Action::"a" in
  > Action::"a"` (where the action literal is the left operand of `.mem`).
  > Policies that used a literal action in any entity-access position
  > failed level checking with `.levelError` even though they were
  > semantically valid. Rust's level checker accepted them, breaking
  > Lean/Rust differential parity.
  > 
  > The fix added the case `.lit (.entityUID euid) _, _ => euid == env.reqty.action`
  > so a literal matching the environment's action passes level checking.
  > This is a *completeness* fix (the buggy validator is over-strict, not
  > unsound), but ETNA's pattern still applies: the witness asserts a
  > known-good policy is accepted, and the variant patch causes the witness
  > to fail with `.levelError`.
- **Fix commit**: `c186f0f4d34c7f244836279e0b4aa6535e1ce252` — Update level checking to allow access to literals equal to environment action (#573)
- **Invariant violated**: For the chosen `(policies, schema, level)` fixture, `validateWithLevel` returns `.ok ()`. (A unit-test-style invariant: the level checker should not over-reject literal action references.)
- **How the mutation triggers**: Replacing `euid == env.reqty.action` with `false` in the literal-entity case of `checkEntityAccessLevel` makes the level checker reject `Action::"a" in Action::"a"`. The witness policy's level check then fails with `.levelError`.

### 9. validator_action_entity_no_attrs

- **Variant**: `validator_action_entity_no_attrs_d7ab5ab_1`
- **Location**: `cedar-lean/Cedar/Validation/RequestEntityValidator.lean:132` (inside `Cedar.Validation.instanceOfSchema.instanceOfActionSchemaEntry`)
- **Property**: `ValidateActionEntityNoAttrs`
- **Witness(es)**:
  - `witness_validate_action_entity_no_attrs_case_action_with_attr` — Action::"a" with attrs={x:1} — fix rejects, bug accepts
- **Source**: [#648](https://github.com/cedar-policy/cedar-spec/pull/648) — Fix validator soundness when `updateSchema` is not used (#648)
  > Validator soundness gap: `validateEntities` did not verify that action
  > entities in the entity store have empty `attrs` (and empty `tags`)
  > unless callers first invoked `updateSchema` to inject synthetic
  > EntitySchemaEntries. Cedar's spec forbids action entities from carrying
  > attributes — without the check, an ill-typed entity store passes
  > validation, breaking the type-soundness assumption used by every
  > authorization theorem in `Thm/Validation/`. The fix folded the action
  > checks directly into `instanceOfSchemaEntry` (combining
  > `instanceOfEntitySchema` and `instanceOfActionSchema` into the new
  > `instanceOfSchema`), removing the `updateSchema` workaround entirely.
- **Fix commit**: `d7ab5abeff0d55f23914b5f2257da8fe3e917002` — Fix validator soundness when `updateSchema` is not used (#648)
- **Invariant violated**: If `validateEntities schema entities = .ok ()`, then every action entity in `entities` (member of any environment's `acts`) has empty `attrs`.
- **How the mutation triggers**: Short-circuiting the `data.attrs == Map.empty` guard in `instanceOfActionSchemaEntry` (changing the test to `(data.attrs == Map.empty) || true`) accepts action entities with non-empty `attrs`. The witness installs `Action::"a"` with `{x: 1}` and observes `validateEntities` returning `.ok ()`.
