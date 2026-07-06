/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import MathlibStaging.Init
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.CategoryTheory.Subfunctor.Basic

/-! -/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

namespace Submodule

variable {M : PresheafOfModules.{v} R} (N : M.Submodule)

/-- The subfunctor of the underlying type-valued presheaf of `M` induced by a submodule `N`. -/
def toSubfunctor : Subfunctor (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{v}) where
  obj X := {r : M.obj X | r ∈ N.obj X}
  map := fun {_ _} f _ hr ↦ N.map_mem f hr

@[simp]
lemma mem_toSubfunctor_obj {X : Cᵒᵖ} (r : M.obj X) :
    r ∈ N.toSubfunctor.obj X ↔ r ∈ N.obj X := Iff.rfl

end Submodule

end PresheafOfModules
