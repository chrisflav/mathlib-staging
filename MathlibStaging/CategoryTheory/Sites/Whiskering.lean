/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Whiskering
public import MathlibStaging.Init

/-!
-/

@[expose] public section

universe v u v₁ u₁

namespace CategoryTheory

open Opposite

variable {C : Type u₁} [Category.{v₁} C] {A : Type u} [Category.{v} A]
  {FA : A → A → Type*} {CA : A → Type v} [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)]
  [ConcreteCategory A FA] (J : GrothendieckTopology C)

/-- If the forgetful functor of a concrete category `A` is corepresentable, then composing an
`A`-valued sheaf with the forgetful functor yields a sheaf of types, i.e. `J.HasSheafCompose`
holds for `forget A`. Unlike `hasSheafCompose_of_preservesLimitsOfSize`, this imposes no
restriction on the universe of the target. -/
instance hasSheafCompose_forget_of_isCorepresentable [(forget A).IsCorepresentable] :
    J.HasSheafCompose (forget A) where
  isSheaf P hP := by
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_iso J (Functor.isoWhiskerLeft P (forget A).coreprW)
      (hP (forget A).coreprX)

end CategoryTheory
