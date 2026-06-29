/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Elab.Tactic.ElabTerm
public meta import Lean.Util.CollectFVars

/-!
# The `generalize_have` and `generalize_let` tactics

`generalize_have` and `generalize_let` behave like `have` and `let`, but before
introducing the new hypothesis they *generalize* it over the local variables it
depends on. Concretely,

```
generalize_have h : T := proof
```

elaborates `proof : T` in the current context, collects the local hypotheses that
`T` and `proof` mention (together with everything those hypotheses depend on), and
introduces

```
h : ∀ x₁ … xₙ, T
```

proved by `fun x₁ … xₙ => proof`, where `x₁ … xₙ` are exactly those local
variables. `generalize_let` does the same but keeps the proof/value visible as a
`let`-binding.

This is useful when refactoring or upstreaming: a fact established with specific
local variables in scope is turned into the standalone, fully general statement,
with the abstracted parameters discovered automatically rather than written out by
hand.

## Restricting the generalization

By default *all* free local variables occurring in the statement and the proof are
generalized. The optional `generalizing` clause restricts generalization to the
listed variables:

```
generalize_have h : T := proof generalizing a b
```

generalizes only over `a` and `b`, leaving every other local variable fixed. It is
an error to ask for a restriction that would produce an ill-typed statement, i.e.
to keep a variable fixed while generalizing another variable that occurs in its
type.
-/

meta section

namespace MathlibStaging.Tactic

open Lean Meta Elab Elab.Tactic

/-- The free variables occurring directly in any of the expressions `es`. -/
private def collectAppearingFVars (es : Array Expr) : Array FVarId :=
  (es.foldl (init := ({} : CollectFVars.State)) collectFVars).fvarIds

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
        | some decl => collectAppearingFVars (#[decl.type] ++ decl.value?.toArray)
        | none => #[]
      downwardClosure lctx seen (deps.toList ++ rest) (out.push f)

/-- Order `fvars` by their position in `lctx`, so that a variable comes after every
variable it may depend on. The result is the array of corresponding free-variable
expressions, suitable for `mkForallFVars`/`mkLambdaFVars`. -/
private def orderFVars (lctx : LocalContext) (fvars : Array FVarId) : Array Expr :=
  let decls := fvars.filterMap lctx.find?
  (decls.qsort (·.index < ·.index)).map (·.toExpr)

/-- The shared implementation of `generalize_have` and `generalize_let`. When
`isLet` is `true` the new declaration is a `let`-binding (its value stays visible),
otherwise it is an opaque hypothesis. -/
private def generalizeHaveLetCore (isLet : Bool) (nm? : Option (TSyntax `ident))
    (tpStx valStx : TSyntax `term) (gens? : Option (Array (TSyntax `ident))) :
    TacticM Unit := withMainContext do
  let name := (nm?.map (·.getId)).getD `this
  -- Elaborate the statement and its proof/value in the current context.
  let tp ← Term.elabType tpStx
  let val ← Term.elabTermEnsuringType valStx tp
  Term.synthesizeSyntheticMVarsNoPostponing
  let tp ← instantiateMVars tp
  let val ← instantiateMVars val
  if val.hasExprMVar || tp.hasExprMVar then
    throwError "`generalize_have`: the statement and its proof must be fully \
      elaborated (no remaining holes) before they can be generalized"
  let lctx ← getLCtx
  let appearing := collectAppearingFVars #[tp, val]
  let toGeneralize ← match gens? with
    | none =>
      -- Generalize over everything the statement/proof depends on.
      pure (downwardClosure lctx {} appearing.toList #[])
    | some gens =>
      -- Restrict to the variables the user listed, after checking that doing so
      -- keeps the statement well-typed.
      let chosen ← gens.mapM getFVarId
      let chosenSet : Std.HashSet FVarId := chosen.foldl (·.insert ·) {}
      for f in appearing do
        unless chosenSet.contains f do
          if let some decl := lctx.find? f then
            if (collectAppearingFVars #[decl.type]).any chosenSet.contains then
              throwError "`generalize_have`: cannot keep `{decl.userName}` fixed while \
                generalizing a variable occurring in its type; add it to the \
                `generalizing` clause"
      pure chosen
  let xs := orderFVars lctx toGeneralize
  let newType ← mkForallFVars xs tp
  let newVal ← mkLambdaFVars xs val
  let goal ← getMainGoal
  let goal ← if isLet then goal.define name newType newVal else goal.assert name newType newVal
  let (_, goal) ← goal.intro1P
  replaceMainGoal [goal]

/-- `generalize_have h : T := proof` is like `have h : T := proof`, but it first
generalizes the new hypothesis over the local variables that `T` and `proof`
depend on, introducing `h : ∀ x₁ … xₙ, T`. The name may be omitted (defaulting to
`this`), and an optional `generalizing a b …` clause restricts the generalization
to the listed variables. See the module doc-string for details. -/
syntax (name := generalizeHave) "generalize_have" (ppSpace ident)? " : " term
  " := " term (ppSpace "generalizing" (ppSpace colGt ident)+)? : tactic

/-- `generalize_let x : T := v` is like `let x : T := v`, but it first generalizes
the new binding over the local variables that `T` and `v` depend on, introducing
the `let`-binding `x : ∀ x₁ … xₙ, T := fun x₁ … xₙ => v`. See `generalize_have` and
the module doc-string for details. -/
syntax (name := generalizeLet) "generalize_let" (ppSpace ident)? " : " term
  " := " term (ppSpace "generalizing" (ppSpace colGt ident)+)? : tactic

elab_rules : tactic
  | `(tactic| generalize_have $[$nm?:ident]? : $tp := $val $[generalizing $gens*]?) =>
    generalizeHaveLetCore (isLet := false) nm? tp val gens

elab_rules : tactic
  | `(tactic| generalize_let $[$nm?:ident]? : $tp := $val $[generalizing $gens*]?) =>
    generalizeHaveLetCore (isLet := true) nm? tp val gens

/-! ## Tests -/

section Tests

-- A statement with no free local variables is introduced unchanged.
example : True := by
  generalize_have h : 1 = 1 := rfl
  guard_hyp h : 1 = 1
  trivial

-- The single local variable occurring in the statement is generalized, and the
-- generalized hypothesis can be re-specialized to close the original goal.
example (n : Nat) : n = n := by
  generalize_have h : n = n := rfl
  guard_hyp h : ∀ n : Nat, n = n
  exact h n

-- An omitted name defaults to `this`.
example (n : Nat) : n = n := by
  generalize_have : n = n := rfl
  guard_hyp this : ∀ n : Nat, n = n
  exact this n

-- Variables occurring only in the *proof* are generalized too, and the
-- generalization order follows the local context (`a`, then `b`, then `hab`).
example (a b : Nat) (hab : a = b) : a = b := by
  generalize_have h : a = b := hab
  guard_hyp h : ∀ (a b : Nat), a = b → a = b
  exact h a b hab

-- `generalizing` restricts the generalization to the listed variables; here `b`
-- stays fixed while `a` is generalized.
example (a b : Nat) : a = b ∨ True := by
  generalize_have h : a = b ∨ True := Or.inr trivial generalizing a
  guard_hyp h : ∀ a : Nat, a = b ∨ True
  exact h a

-- `generalize_let` keeps the value visible as a `let`-binding.
example (n : Nat) : n = n := by
  generalize_let f : Nat → Nat := fun k => k + n
  guard_hyp f : ∀ _ : Nat, Nat → Nat := fun n k => k + n
  rfl

-- Restricting in a way that would make the statement ill-typed is rejected: `h2`
-- is kept fixed but mentions the generalized variables `a` and `b` in its type.
/--
error: `generalize_have`: cannot keep `h2` fixed while generalizing a variable occurring in its type; add it to the `generalizing` clause
-/
#guard_msgs in
example (a b : Nat) (h2 : a = b) : True := by
  generalize_have h : a = b := h2 generalizing a b
  trivial

end Tests

end MathlibStaging.Tactic
