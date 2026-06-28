/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import MathlibStaging.Init

/-!
# The restriction maps of a presheaf of modules as semilinear maps

The restriction map `M.map f` of a presheaf of modules `M` along `f : X ⟶ Y` has codomain the
module obtained from `M.obj Y` by restriction of scalars along `R.map f`. We bundle it as a
genuine semilinear map `M.restrictₛₗ f : M.obj X →ₛₗ[(R.map f).hom] M.obj Y`, which is often more
convenient to work with.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- The restriction map `M.map f` of a presheaf of modules `M`, bundled as a semilinear map
along the ring map `R.map f`. -/
noncomputable def restrictₛₗ (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    M.obj X →ₛₗ[(R.map f).hom] M.obj Y where
  toFun m := M.map f m
  map_add' := map_add (M.map f).hom
  map_smul' r m := M.map_smul f r m

@[simp]
lemma restrictₛₗ_apply (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.obj X) :
    M.restrictₛₗ f m = M.map f m := rfl

end PresheafOfModules
