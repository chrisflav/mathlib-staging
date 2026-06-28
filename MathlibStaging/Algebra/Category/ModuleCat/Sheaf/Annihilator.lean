/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import MathlibStaging.Init
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import MathlibStaging.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Subsheaf
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

-/

@[expose] public section

universe v v₁ u₁ u w

open CategoryTheory Opposite

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (M : PresheafOfModules.{v} R)

/-- The annihilator ideal of `M` at `X`: those sections `r` of `R` over `X`
whose restriction along every `f : X ⟶ Y` annihilates `M.obj Y`. -/
def annihilatorIdeal (X : Cᵒᵖ) : Ideal (R.obj X) where
  carrier := { r | ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (m : M.obj Y), R.map f r • m = 0 }
  zero_mem' Y f m := by rw [map_zero, zero_smul]
  add_mem' {a b} ha hb Y f m := by rw [map_add, add_smul, ha f m, hb f m, add_zero]
  smul_mem' c r hr Y f m := by rw [smul_eq_mul, map_mul, mul_smul, hr f m, smul_zero]

variable {M}

@[simp]
lemma mem_annihilatorIdeal {X : Cᵒᵖ} (r : R.obj X) :
    r ∈ M.annihilatorIdeal X ↔
      ∀ ⦃Y : Cᵒᵖ⦄ (f : X ⟶ Y) (m : M.obj Y), R.map f r • m = 0 :=
  Iff.rfl

variable (M)

/-- The annihilator of `M`, as a family of submodules of `unit R` stable under
restriction. -/
noncomputable def annihilatorSystem : (unit R).Submodule where
  obj X := M.annihilatorIdeal X
  map {X Y} f := by
    intro r hr
    rw [Submodule.mem_comap, restrictₛₗ_apply]
    refine (mem_annihilatorIdeal _).mpr fun Z g m ↦ ?_
    have h := (mem_annihilatorIdeal _).mp hr (f ≫ g) m
    rwa [R.map_comp, RingCat.comp_apply] at h

/-- The annihilator of a presheaf of modules `M`, a sub-presheaf of modules of
`unit R`. -/
noncomputable def annihilator : PresheafOfModules.{u} R :=
  M.annihilatorSystem.toPresheafOfModules

/-- The inclusion of the annihilator of `M` into `unit R`. -/
noncomputable def annihilatorι : M.annihilator ⟶ unit R :=
  M.annihilatorSystem.ι

instance : Mono M.annihilatorι :=
  inferInstanceAs (Mono M.annihilatorSystem.ι)

variable {M}

@[simp]
lemma annihilatorι_app_apply (X : Cᵒᵖ) (r : (M.annihilatorSystem.obj X)) :
    M.annihilatorι.app X r = r.val := rfl

/-- The annihilator is antitone with respect to morphisms that are surjective on sections:
if `f : M ⟶ N` is componentwise surjective, then everything annihilating `M` annihilates `N`. -/
lemma annihilatorIdeal_le_of_surjective {M N : PresheafOfModules.{v} R} (f : M ⟶ N)
    (hf : ∀ Y, Function.Surjective (f.app Y)) (X : Cᵒᵖ) :
    M.annihilatorIdeal X ≤ N.annihilatorIdeal X := by
  intro r hr
  refine (mem_annihilatorIdeal r).mpr fun Y g n ↦ ?_
  obtain ⟨m, rfl⟩ := hf Y n
  have hlin : f.app Y (R.map g r • m) = R.map g r • f.app Y m := (f.app Y).hom.map_smul _ _
  rw [← hlin, (mem_annihilatorIdeal r).mp hr g m]
  exact (f.app Y).hom.map_zero

end PresheafOfModules

namespace SheafOfModules

open PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- The underlying type-valued presheaf of an `AddCommGrpCat`-valued sheaf is a sheaf of types.
This holds at any universe `w`, since the forgetful functor of `AddCommGrpCat.{w}` is
corepresentable (by `ULift.{w} ℤ`); in particular it does not require `w = max v₁ u₁`. -/
private lemma presieveIsSheaf_comp_forget {A : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (h : Presheaf.IsSheaf J A) :
    Presieve.IsSheaf J (A ⋙ CategoryTheory.forget AddCommGrpCat.{w}) :=
  Presieve.isSheaf_iso J (Functor.isoWhiskerLeft A AddCommGrpCat.coyonedaObjIsoForget)
    (h (AddCommGrpCat.of (ULift.{w} ℤ)))

variable
  [J.HasSheafCompose (forget₂ RingCat.{max v₁ u₁} AddCommGrpCat.{max v₁ u₁})]
  {R : Sheaf J RingCat.{max v₁ u₁}} (M : SheafOfModules.{v} R)

/-- The annihilator of a sheaf of modules `M`, as a sheaf of modules: a subobject of
`unit R` whose sections over `X` are those `r : R.obj X` annihilating `M` locally. -/
noncomputable def annihilator : SheafOfModules.{max v₁ u₁} R where
  val := M.val.annihilator
  isSheaf := by
    -- The underlying type-valued presheaf of `unit R`, which is a sheaf.
    let F : Cᵒᵖ ⥤ Type (max v₁ u₁) :=
      (PresheafOfModules.unit R.obj).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{max v₁ u₁}
    have hF : Presieve.IsSheaf J F :=
      presieveIsSheaf_comp_forget (SheafOfModules.unit R).isSheaf
    -- The annihilator as a subfunctor of `F`.
    let G : Subfunctor F :=
      { obj := fun X ↦ { r : R.obj.obj X | r ∈ M.val.annihilatorIdeal X }
        map := fun {U V} i r hr ↦ M.val.annihilatorSystem.map_mem i hr }
    -- `M.val` is separated, as the underlying type-valued presheaf of a sheaf.
    have hsep : Presieve.IsSheaf J (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{v}) :=
      presieveIsSheaf_comp_forget M.isSheaf
    -- The annihilator subfunctor is a sheaf: it is closed under the topology.
    have hG : Presieve.IsSheaf J G.toFunctor := by
      rw [G.isSheaf_iff hF]
      intro U s hs W φ m
      -- Pull back the covering sieve along the morphism underlying `φ`.
      have hpb : Sieve.pullback φ.unop (G.sieveOfSection s) ∈ J W.unop :=
        J.pullback_stable φ.unop hs
      -- It suffices, by separatedness, that every restriction of `R.map φ s • m` vanishes.
      apply (hsep _ hpb).isSeparatedFor.ext
      intro Y f hf
      -- On the pulled-back sieve, the relevant section lies in the annihilator ideal.
      have hcomp : (f ≫ φ.unop).op = φ ≫ f.op := by rw [op_comp, Quiver.Hom.op_unop]
      have key : R.obj.map (φ ≫ f.op) s ∈ M.val.annihilatorIdeal (op Y) := by
        rw [← hcomp]; exact hf
      -- Hence it annihilates the restriction of `m`.
      have h0 : R.obj.map (φ ≫ f.op) s • M.val.map f.op m = 0 := by
        have h := (mem_annihilatorIdeal _).mp key (𝟙 (op Y))
          (M.val.map f.op m : M.val.obj (op Y))
        rwa [R.obj.map_id, RingCat.id_apply] at h
      suffices M.val.map f.op (R.obj.map φ s • m) = M.val.map f.op 0 by exact this
      rw [map_zero, M.val.map_smul, ← RingCat.comp_apply, ← R.obj.map_comp, h0]
    -- Transfer the sheaf condition back to `M.val.annihilator.presheaf`.
    rw [Presheaf.isSheaf_iff_isSheaf_forget (J := J)
        (s := CategoryTheory.forget AddCommGrpCat.{max v₁ u₁}),
      isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_iso J (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)) hG

/-- The inclusion of the annihilator of `M` into `unit R`. -/
noncomputable def annihilatorι : M.annihilator ⟶ unit R :=
  ⟨M.val.annihilatorι⟩

end SheafOfModules
