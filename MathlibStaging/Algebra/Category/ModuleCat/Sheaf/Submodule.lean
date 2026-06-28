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

Given a sheaf of modules `P`, a `SheafOfModules.Submodule P` is a submodule `N` of its underlying
presheaf of modules whose membership is *local*.
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

/-- A submodule of a sheaf of modules `P`: a submodule `N` of the underlying presheaf of modules
whose membership is *local*. Locality means that if a section `s` restricts into `N` along a
covering sieve, then `s` already lies in `N`; this is exactly the condition making
`N.toPresheafOfModules` a sheaf. -/
structure Submodule (P : SheafOfModules.{v} R) extends P.val.Submodule where
  /-- Membership in the submodule is local. -/
  isSheaf ⦃X : Cᵒᵖ⦄ (s : P.val.obj X) :
    toSubmodule.toSubfunctor.sieveOfSection s ∈ J X.unop → s ∈ toSubmodule.obj X

namespace Submodule

variable {P : SheafOfModules.{v} R} (N : P.Submodule)

/-- The sheaf of modules associated to a submodule of a sheaf of modules. -/
noncomputable def toSheafOfModules : SheafOfModules.{v} R where
  val := N.toPresheafOfModules
  isSheaf := by
    have hF : Presieve.IsSheaf J (P.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{v}) :=
      (isSheaf_iff_isSheaf_of_type J _).mp
        (GrothendieckTopology.HasSheafCompose.isSheaf _ P.isSheaf)
    have hG : Presieve.IsSheaf J N.toSubfunctor.toFunctor := by
      rw [N.toSubfunctor.isSheaf_iff hF]
      exact N.isSheaf
    apply Presheaf.isSheaf_of_isSheaf_comp J (s := CategoryTheory.forget AddCommGrpCat.{v})
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_iso J (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by cat_disch)) hG

/-- The inclusion of the sheaf of modules associated to a submodule `N` into `P`. -/
noncomputable def ι : N.toSheafOfModules ⟶ P :=
  ⟨N.toSubmodule.ι⟩

instance : Mono N.ι := by
  have : Mono ((forget R).map N.ι) := inferInstanceAs (Mono N.toSubmodule.ι)
  exact (forget R).mono_of_mono_map this

end Submodule

end SheafOfModules
