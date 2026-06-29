/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import MathlibStaging.Init
public import MathlibStaging.Algebra.Category.ModuleCat.Presheaf.Submodule
public import MathlibStaging.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.RingTheory.Ideal.Maps

/-!
# The annihilator ideal (pre)sheaf of a (pre)sheaf of modules

Given a presheaf of modules `M` over a presheaf of rings `R`, we define the
annihilator `PresheafOfModules.annihilator M`, a sub-presheaf of modules of the
unit `unit R` (i.e. `R` viewed as a module over itself). Its sections over `X`
are the sections `r` of `R` whose restriction along every `f : X ⟶ Y`
annihilates `M.obj Y`. Equivalently, this is the kernel of the action of `R`
on `M` computed in the internal hom; phrasing it via restrictions avoids relying
on an internal hom for sheaves of modules.

When `R` is a sheaf of rings and `M` a sheaf of modules, the annihilator is a
sheaf, giving `SheafOfModules.annihilator M` together with its inclusion
monomorphism into `unit R`.

## Main definitions

- `PresheafOfModules.annihilator M`: the annihilator as a submodule of `unit R`.
- `SheafOfModules.annihilator M`: the annihilator as a submodule of `unit R` in the sense of
  `SheafOfModules.Submodule`, with inclusion `M.annihilator.ι` into `unit R`.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{v} R)

/-- Membership in the annihilator `iInf`, characterised at the honest type `R.obj X`. This is the
content of `mem_annihilator`; it is split out so that it can also be used in the construction of
`annihilator` itself (where its sections do not yet have the `unit R` module structure attached). -/
private lemma mem_annihilator_iInf {X : Cᵒᵖ} (r : R.obj X) :
    r ∈ (⨅ (Y : Cᵒᵖ) (f : X ⟶ Y),
        (Module.annihilator (R.obj Y) (M.obj Y)).comap (R.map f).hom) ↔
      ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (m : M.obj Y), R.map f r • m = 0 := by
  simp only [Submodule.mem_iInf, Ideal.mem_comap, Module.mem_annihilator]

/-- The annihilator of a presheaf of modules `M`, as a submodule of `unit R`: its sections over
`X` are those sections `r` of `R` annihilating `M` along every restriction. Over `X` it is the
intersection over all `f : X ⟶ Y` of the pullbacks of the pointwise annihilators
`Module.annihilator (R.obj Y) (M.obj Y)`. -/
noncomputable def annihilator : (unit R).Submodule where
  obj X := ⨅ (Y : Cᵒᵖ) (f : X ⟶ Y),
    (Module.annihilator (R.obj Y) (M.obj Y)).comap (R.map f).hom
  map {X Y} f := by
    intro r hr
    rw [Submodule.mem_comap, restrictₛₗ_apply]
    refine (mem_annihilator_iInf M _).mpr fun Z g m ↦ ?_
    have h := (mem_annihilator_iInf M _).mp hr (f ≫ g) m
    rwa [R.map_comp, RingCat.comp_apply] at h

variable {M}

lemma mem_annihilator {X : Cᵒᵖ} (r : (unit R).obj X) :
    r ∈ M.annihilator.obj X ↔
      ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (m : M.obj Y), R.map f r • m = 0 :=
  mem_annihilator_iInf M r

/-- The annihilator is antitone with respect to morphisms that are surjective on sections:
if `f : M ⟶ N` is componentwise surjective, then everything annihilating `M` annihilates `N`. -/
lemma annihilator_le_of_surjective {M N : PresheafOfModules.{v} R} (f : M ⟶ N)
    (hf : ∀ Y, Function.Surjective (f.app Y)) (X : Cᵒᵖ) :
    M.annihilator.obj X ≤ N.annihilator.obj X := by
  intro r hr
  rw [mem_annihilator] at hr ⊢
  intro Y g n
  obtain ⟨m, rfl⟩ := hf Y n
  rw [← (f.app Y).hom.map_smul, hr g m]
  exact (f.app Y).hom.map_zero

end PresheafOfModules

namespace SheafOfModules

open PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

variable
  [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
  {R : Sheaf J RingCat.{u}}

variable (M : SheafOfModules.{v} R)

/-- The annihilator of a sheaf of modules `M`, as a submodule of `unit R`: a subobject whose
sections over `X` are those `r : R.obj X` annihilating `M` locally. The associated sheaf of
modules is `M.annihilator.toSheafOfModules`. -/
noncomputable def annihilator : (SheafOfModules.unit R).Submodule where
  toSubmodule := M.val.annihilator
  isSheaf := by
    have hsep : Presieve.IsSheaf J (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{v}) :=
      (isSheaf_iff_isSheaf_of_type J _).mp
        (GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf)
    intro X s hmem
    refine (mem_annihilator s).mpr fun W φ m ↦ ?_
    -- It suffices, by separatedness, that every restriction of `R.map φ s • m` vanishes.
    apply (hsep _ (J.pullback_stable φ.unop hmem)).isSeparatedFor.ext
    intro Y f hf
    -- On the pulled-back sieve, the relevant section lies in the annihilator ideal.
    have hcomp : (f ≫ φ.unop).op = φ ≫ f.op := by rw [op_comp, Quiver.Hom.op_unop]
    have key : R.obj.map (φ ≫ f.op) s ∈ M.val.annihilator.obj (op Y) := by
      rw [← hcomp]
      exact hf
    -- Hence it annihilates the restriction of `m` (the goal here is, definitionally, this
    -- equation phrased through the forgetful functor to types).
    have h0 : R.obj.map (φ ≫ f.op) s • M.val.map f.op m = 0 := by
      have h := (mem_annihilator _).mp key (𝟙 (op Y)) (M.val.map f.op m)
      rwa [R.obj.map_id, RingCat.id_apply] at h
    have : M.val.map f.op (R.obj.map φ s • m) = M.val.map f.op 0 := by
      rw [map_zero, M.val.map_smul, ← RingCat.comp_apply, ← R.obj.map_comp, h0]
    exact this

end SheafOfModules
