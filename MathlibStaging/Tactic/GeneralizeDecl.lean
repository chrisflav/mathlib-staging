/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Util.CollectFVars
public import MathlibStaging.Init

/-!
# The `generalize_decl` tactic

`generalize_decl at h` *generalizes* an existing local declaration `h` over the
local variables it depends on. Concretely, if the context contains

```
let h : T := proof
```

then `generalize_decl at h` collects the local hypotheses that `T` and `proof`
mention (together with everything those hypotheses depend on) and replaces `h`
with the standalone hypothesis

```
h : ∀ x₁ … xₙ, T
```

proved by `fun x₁ … xₙ => proof`, where `x₁ … xₙ` are exactly those local
variables.

This is useful when refactoring or upstreaming: a fact established with specific
local variables in scope is turned into the standalone, fully general statement,
with the abstracted parameters discovered automatically rather than written out by
hand.

## Recoverable proofs are required

Generalizing `h : T` to `∀ x₁ … xₙ, T` requires re-abstracting the *proof* of `h`,
so the proof must still be available in the local context. This is the case for
`let`-bindings (whose value is kept) but **not** for opaque `have`-hypotheses
(whose proof is discarded once the hypothesis is introduced). Introduce the
declaration you want to generalize with `let` rather than `have`; applying
`generalize_decl` to an opaque hypothesis raises an error.

## Restricting the generalization

By default *all* free local variables occurring in the statement and the proof are
generalized. The optional `generalizing` clause restricts generalization to the
listed variables:

```
generalize_decl at h generalizing a b
```

generalizes only over `a` and `b`, leaving every other local variable fixed. When
a variable is generalized, every (relevant) variable depending on it is generalized
as well — this is forced for the resulting statement to stay well-typed.
-/

meta section

namespace MathlibStaging.Tactic

open Lean Meta Elab Elab.Tactic

/-- The free variables occurring directly in any of the expressions `es`. -/
private def collectAppearingFVars (es : Array Expr) : Array FVarId :=
  (es.foldl (init := ({} : CollectFVars.State)) collectFVars).fvarIds

/-- The local variables the declaration `decl` directly depends on: the free
variables of its type and, for `let`-bindings, of its value. -/
private def declDeps (decl : LocalDecl) : Array FVarId :=
  collectAppearingFVars (#[decl.type] ++ decl.value?.toArray)

/-- Close `fvars` downwards under the dependency relation in `lctx`: the result
contains every variable in `fvars` together with every local variable occurring in
the type (or, for `let`-bindings, the value) of a variable already in the set.
This is the set that must be abstracted to keep the resulting `∀`-statement
well-typed. -/
private partial def downwardClosure (lctx : LocalContext) (seen : Std.HashSet FVarId)
    (todo : List FVarId) (out : Array FVarId) : Array FVarId :=
  match todo with
  | [] => out
  | f :: rest =>
    if seen.contains f then
      downwardClosure lctx seen rest out
    else
      let seen := seen.insert f
      let deps := match lctx.find? f with
        | some decl => declDeps decl
        | none => #[]
      downwardClosure lctx seen (deps.toList ++ rest) (out.push f)

/-- Compute the set of variables to abstract when the user restricts the
generalization to `chosen`. Starting from `chosen`, this repeatedly adds every
*relevant* variable whose type or value depends on a variable already chosen
(keeping such a variable fixed while generalizing one occurring in its type would
be ill-typed), and finally closes the whole set downwards so that `mkForallFVars`
stays well-typed. `relevant` is the set of variables reachable from the statement
and proof, i.e. the only ones whose fixedness can matter. -/
private def restrictedGeneralization (lctx : LocalContext) (relevant : Array FVarId)
    (chosen : Array FVarId) : Array FVarId := Id.run do
  let mut seen : Std.HashSet FVarId := chosen.foldl (·.insert ·) {}
  let mut changed := true
  while changed do
    changed := false
    for f in relevant do
      unless seen.contains f do
        if let some decl := lctx.find? f then
          if (declDeps decl).any seen.contains then
            seen := seen.insert f
            changed := true
  return downwardClosure lctx {} seen.toList #[]

/-- Order `fvars` by their position in `lctx`, so that a variable comes after every
variable it may depend on. The result is the array of corresponding free-variable
expressions, suitable for `mkForallFVars`/`mkLambdaFVars`. -/
private def orderFVars (lctx : LocalContext) (fvars : Array FVarId) : Array Expr :=
  let decls := fvars.filterMap lctx.find?
  (decls.qsort (·.index < ·.index)).map (·.toExpr)

/-- The implementation of `generalize_decl at h`. Generalizes the existing local
declaration `h` over the local variables its type and value depend on, replacing it
with the generalized declaration of the same name. -/
private def generalizeDeclCore (hStx : TSyntax `ident)
    (gens? : Option (Array (TSyntax `ident))) : TacticM Unit := withMainContext do
  let fvarId ← getFVarId hStx
  let lctx ← getLCtx
  let decl := lctx.get! fvarId
  let some val := decl.value?
    | throwError "`generalize_decl`: `{decl.userName}` is an opaque hypothesis whose \
        proof is not available, so it cannot be generalized. Introduce it with `let` \
        instead of `have` so that its proof is kept in the context."
  let tp ← instantiateMVars decl.type
  let val ← instantiateMVars val
  if val.hasExprMVar || tp.hasExprMVar then
    throwError "`generalize_decl`: the statement and proof of `{decl.userName}` must \
      be fully elaborated (no remaining holes) before they can be generalized"
  -- The variables `tp` and `val` mention, excluding `h` itself, together with
  -- everything they depend on.
  let appearing := (collectAppearingFVars #[tp, val]).filter (· != fvarId)
  let relevant := downwardClosure lctx {} appearing.toList #[]
  let toGeneralize ← match gens? with
    | none =>
      -- Generalize over everything the statement/proof depends on.
      pure relevant
    | some gens =>
      -- Restrict to the variables the user listed, also generalizing every variable
      -- depending on them so that the statement stays well-typed.
      let chosen ← gens.mapM getFVarId
      pure (restrictedGeneralization lctx relevant chosen)
  let toGeneralize := toGeneralize.filter (· != fvarId)
  let xs := orderFVars lctx toGeneralize
  let newType ← mkForallFVars xs tp
  let newVal ← mkLambdaFVars xs val
  let goal ← getMainGoal
  let goal ← goal.assert decl.userName newType newVal
  let (_, goal) ← goal.intro1P
  -- Remove the original, non-generalized declaration.
  let goal ← goal.tryClear fvarId
  replaceMainGoal [goal]

/-- `generalize_decl at h` generalizes the existing local declaration `h` over the
local variables that its statement and proof depend on, replacing `h : T` with
`h : ∀ x₁ … xₙ, T`. The declaration must carry a recoverable proof, i.e. be a
`let`-binding rather than an opaque `have`. An optional `generalizing a b …` clause
restricts the generalization to the listed variables. See the module doc-string for
details. -/
syntax (name := generalizeDecl) "generalize_decl" " at " ident
  (ppSpace "generalizing" (ppSpace colGt ident)+)? : tactic

elab_rules : tactic
  | `(tactic| generalize_decl at $h:ident $[generalizing $gens*]?) =>
    generalizeDeclCore h gens

/-! ## Tests -/

section Tests

-- A declaration with no free local variables is generalized to itself.
example : True := by
  let h : (1 : Nat) = 1 := rfl
  generalize_decl at h
  guard_hyp h : 1 = 1
  trivial

-- The single local variable occurring in the statement is generalized, and the
-- generalized declaration can be re-specialized to close the original goal.
example (n : Nat) : n = n := by
  let h : n = n := rfl
  generalize_decl at h
  guard_hyp h : ∀ n : Nat, n = n
  exact h n

-- Variables occurring only in the *proof* are generalized too, and the
-- generalization order follows the local context (`a`, then `b`, then `hab`).
example (a b : Nat) (hab : a = b) : a = b := by
  let h : a = b := hab
  generalize_decl at h
  guard_hyp h : ∀ (a b : Nat), a = b → a = b
  exact h a b hab

-- `generalizing` restricts the generalization to the listed variables; here `b`
-- stays fixed while `a` is generalized.
example (a b : Nat) : a = a ∨ b = b := by
  let h : a = a ∨ b = b := Or.inl rfl
  generalize_decl at h generalizing a
  guard_hyp h : ∀ a : Nat, a = a ∨ b = b
  exact h a

-- When generalizing a variable, every variable depending on it is generalized as
-- well (instead of raising an error): `generalizing a` also generalizes `h2 : a = b`
-- and, in turn, `b`.
example (a b : Nat) (h2 : a = b) : True := by
  let h : a = b := h2
  generalize_decl at h generalizing a
  guard_hyp h : ∀ (a b : Nat), a = b → a = b
  trivial

-- Generalization also works for `let`-bound data, abstracting over variables that
-- occur only in the value.
example (n : Nat) : n = n := by
  let f : Nat → Nat := fun k => k + n
  generalize_decl at f
  guard_hyp f : ∀ _ : Nat, Nat → Nat
  rfl

-- An opaque `have` cannot be generalized: its proof is not recoverable.
/--
error: `generalize_decl`: `h` is an opaque hypothesis whose proof is not available, so it cannot be generalized. Introduce it with `let` instead of `have` so that its proof is kept in the context.
-/
#guard_msgs in
example (n : Nat) : True := by
  have h : n = n := rfl
  generalize_decl at h
  trivial

end Tests

end MathlibStaging.Tactic
