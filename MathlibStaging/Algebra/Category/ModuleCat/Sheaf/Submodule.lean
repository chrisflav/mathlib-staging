/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import MathlibStaging.Init
public import MathlibStaging.Algebra.Category.ModuleCat.Presheaf.Submodule
public import MathlibStaging.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Submodules of sheaves of modules

Given a sheaf of modules `M`, a `SheafOfModules.Submodule M` is a submodule `N` of its underlying
presheaf of modules whose membership condition is local.
`N.toPresheafOfModules` is then again a sheaf, giving `N.toSheafOfModules`.

## Main definitions

- `SheafOfModules.Submodule`: a submodule of (the underlying presheaf of modules of) a sheaf of
  modules whose membership is local.
- `SheafOfModules.Submodule.toSheafOfModules`: the associated sheaf of modules.
- `SheafOfModules.Submodule.ι`: the inclusion of `N.toSheafOfModules` into `P`, a monomorphism.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Opposite

namespace SheafOfModules

open PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- A submodule of a sheaf of modules `M`: a submodule `N` of the underlying presheaf of modules
whose membership condition is local. Locality means that if a section `s` restricts into `N` along a
covering sieve, then `s` already lies in `N`; this is exactly the condition making
`N.toPresheafOfModules` a sheaf. -/
structure Submodule (M : SheafOfModules.{v} R) extends M.val.Submodule where
  /-- Membership in the submodule is local. -/
  isSheaf ⦃X : Cᵒᵖ⦄ (s : M.val.obj X) :
    toSubmodule.toSubfunctor.sieveOfSection s ∈ J X.unop → s ∈ toSubmodule.obj X

namespace Submodule

variable {M : SheafOfModules.{v} R} (N : M.Submodule)

/-- The sheaf of modules associated to a submodule of a sheaf of modules. -/
noncomputable def toSheafOfModules : SheafOfModules.{v} R where
  val := N.toPresheafOfModules
  isSheaf := by
    have hF : Presieve.IsSheaf J (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{v}) :=
      (isSheaf_iff_isSheaf_of_type J _).mp
        (GrothendieckTopology.HasSheafCompose.isSheaf _ M.isSheaf)
    have hG : Presieve.IsSheaf J N.toSubfunctor.toFunctor := by
      rw [N.toSubfunctor.isSheaf_iff hF]
      exact N.isSheaf
    apply Presheaf.isSheaf_of_isSheaf_comp J (s := CategoryTheory.forget AddCommGrpCat.{v})
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_iso J (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by cat_disch)) hG

/-- The inclusion of the sheaf of modules associated to a submodule `N` into `M`. -/
noncomputable def ι : N.toSheafOfModules ⟶ M :=
  ⟨N.toSubmodule.ι⟩

@[simp]
lemma ι_val : N.ι.val = N.toSubmodule.ι := rfl

instance : Mono N.ι := by
  have : Mono ((forget R).map N.ι) := inferInstanceAs (Mono N.toSubmodule.ι)
  exact (forget R).mono_of_mono_map this

@[ext]
lemma ext {N₁ N₂ : M.Submodule} (h : N₁.toSubmodule = N₂.toSubmodule) : N₁ = N₂ := by
  cases N₁
  cases N₂
  congr

instance : PartialOrder M.Submodule :=
  PartialOrder.lift _ fun _ _ ↦ ext

lemma le_iff {N₁ N₂ : M.Submodule} : N₁ ≤ N₂ ↔ N₁.toSubmodule ≤ N₂.toSubmodule := .rfl

/-- The infimum of a family of submodules of a sheaf of modules: the underlying presheaf submodule
is the infimum of the underlying presheaf submodules, which is again local. -/
instance : InfSet M.Submodule where
  sInf s :=
    { toSubmodule := sInf ((·.toSubmodule) '' s)
      isSheaf := fun X x hx ↦ by
        simp only [PresheafOfModules.Submodule.sInf_obj, Submodule.mem_iInf]
        rintro _ ⟨N', hN', rfl⟩
        refine N'.isSheaf x (J.superset_covering (fun V f hf ↦ ?_) hx)
        have h := sInf_le (Set.mem_image_of_mem (·.toSubmodule) hN')
        exact PresheafOfModules.Submodule.le_iff.mp h (op V) hf }

/-- The submodules of a sheaf of modules form a complete lattice, induced from the complete lattice
of submodules of the underlying presheaf of modules via the local infima. -/
noncomputable instance : CompleteLattice M.Submodule :=
  completeLatticeOfInf M.Submodule fun s ↦
    ⟨fun _ hN ↦ le_iff.mpr (sInf_le (Set.mem_image_of_mem _ hN)),
      fun _ hb ↦ le_iff.mpr <| le_sInf <| by
        rintro _ ⟨N', hN', rfl⟩
        exact le_iff.mp (hb hN')⟩

end Submodule

end SheafOfModules
