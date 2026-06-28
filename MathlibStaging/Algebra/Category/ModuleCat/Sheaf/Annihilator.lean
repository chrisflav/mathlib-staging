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

- `PresheafOfModules.annihilatorIdeal M X`: the annihilator ideal of `M` at `X`.
- `PresheafOfModules.annihilator M`: the annihilator as a submodule of `unit R`.
- `SheafOfModules.annihilator M`: the annihilator as a submodule of `unit R` in the sense of
  `SheafOfModules.Submodule`, with inclusion `SheafOfModules.annihilatorι M`.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{v} R)

/-- The annihilator ideal of `M` at `X`: those sections `r` of `R` over `X`
whose restriction along every `f : X ⟶ Y` annihilates `M.obj Y`. It is the
intersection over all `f : X ⟶ Y` of the pullbacks of the pointwise annihilators
`Module.annihilator (R.obj Y) (M.obj Y)`. -/
def annihilatorIdeal (X : Cᵒᵖ) : Ideal (R.obj X) :=
  ⨅ (Y : Cᵒᵖ) (f : X ⟶ Y),
    (Module.annihilator (R.obj Y) (M.obj Y)).comap (R.map f).hom

variable {M}

lemma mem_annihilatorIdeal {X : Cᵒᵖ} (r : R.obj X) :
    r ∈ M.annihilatorIdeal X ↔
      ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (m : M.obj Y), R.map f r • m = 0 := by
  simp only [annihilatorIdeal, Submodule.mem_iInf, Ideal.mem_comap, Module.mem_annihilator]

variable (M)

/-- The annihilator of a presheaf of modules `M`, as a submodule of `unit R`: its sections over
`X` are those sections `r` of `R` annihilating `M` along every restriction. -/
noncomputable def annihilator : (unit R).Submodule where
  obj X := M.annihilatorIdeal X
  map {X Y} f := by
    intro r hr
    rw [Submodule.mem_comap, restrictₛₗ_apply]
    refine (mem_annihilatorIdeal _).mpr fun Z g m ↦ ?_
    have h := (mem_annihilatorIdeal _).mp hr (f ≫ g) m
    rwa [R.map_comp, RingCat.comp_apply] at h

variable {M}

/-- The annihilator is antitone with respect to morphisms that are surjective on sections:
if `f : M ⟶ N` is componentwise surjective, then everything annihilating `M` annihilates `N`. -/
lemma annihilatorIdeal_le_of_surjective {M N : PresheafOfModules.{v} R} (f : M ⟶ N)
    (hf : ∀ Y, Function.Surjective (f.app Y)) (X : Cᵒᵖ) :
    M.annihilatorIdeal X ≤ N.annihilatorIdeal X := by
  intro r hr
  refine (mem_annihilatorIdeal r).mpr fun Y g n ↦ ?_
  obtain ⟨m, rfl⟩ := hf Y n
  rw [← (f.app Y).hom.map_smul, (mem_annihilatorIdeal r).mp hr g m]
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
    refine (mem_annihilatorIdeal s).mpr fun W φ m ↦ ?_
    -- It suffices, by separatedness, that every restriction of `R.map φ s • m` vanishes.
    apply (hsep _ (J.pullback_stable φ.unop hmem)).isSeparatedFor.ext
    intro Y f hf
    -- On the pulled-back sieve, the relevant section lies in the annihilator ideal.
    have hcomp : (f ≫ φ.unop).op = φ ≫ f.op := by rw [op_comp, Quiver.Hom.op_unop]
    have key : R.obj.map (φ ≫ f.op) s ∈ M.val.annihilatorIdeal (op Y) := by
      rw [← hcomp]
      exact hf
    -- Hence it annihilates the restriction of `m` (the goal here is, definitionally, this
    -- equation phrased through the forgetful functor to types).
    have h0 : R.obj.map (φ ≫ f.op) s • M.val.map f.op m = 0 := by
      have h := (mem_annihilatorIdeal _).mp key (𝟙 (op Y)) (M.val.map f.op m)
      rwa [R.obj.map_id, RingCat.id_apply] at h
    have : M.val.map f.op (R.obj.map φ s • m) = M.val.map f.op 0 := by
      rw [map_zero, M.val.map_smul, ← RingCat.comp_apply, ← R.obj.map_comp, h0]
    exact this

/-- The inclusion of the annihilator of `M` into `unit R`. -/
noncomputable def annihilatorι : M.annihilator.toSheafOfModules ⟶ unit R :=
  ⟨M.val.annihilator.ι⟩

instance : Mono M.annihilatorι := by
  have : Mono ((forget R).map M.annihilatorι) := inferInstanceAs (Mono M.val.annihilator.ι)
  exact (forget R).mono_of_mono_map this

end SheafOfModules
