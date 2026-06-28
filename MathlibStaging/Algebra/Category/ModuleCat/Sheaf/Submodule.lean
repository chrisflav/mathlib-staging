/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import MathlibStaging.Init
public import MathlibStaging.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Sheaves of modules cut out by a local submodule

Given a sheaf of modules `P` and a submodule `N` of its underlying presheaf of modules whose
membership is *local*, the associated presheaf of modules `N.toPresheafOfModules` is again a
sheaf. This is the general glue used to construct subobjects of sheaves of modules from
submodules of the underlying presheaf of modules.

## Main definitions

- `SheafOfModules.ofLocalSubmodule`: a submodule of (the underlying presheaf of modules of) a
  sheaf of modules whose membership is local is a sheaf of modules.
-/

@[expose] public section

universe v v₁ u₁ u w

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- The underlying type-valued presheaf of an `AddCommGrpCat`-valued sheaf is a sheaf of types.
This holds at any universe `w`, since the forgetful functor of `AddCommGrpCat.{w}` is
corepresentable (by `ULift.{w} ℤ`); in particular it does not require `w = max v₁ u₁`. -/
lemma isSheaf_comp_forget {A : Cᵒᵖ ⥤ AddCommGrpCat.{w}}
    (h : Presheaf.IsSheaf J A) :
    Presieve.IsSheaf J (A ⋙ forget AddCommGrpCat.{w}) :=
  Presieve.isSheaf_iso J (Functor.isoWhiskerLeft A AddCommGrpCat.coyonedaObjIsoForget)
    (h (AddCommGrpCat.of (ULift.{w} ℤ)))

end CategoryTheory.Presheaf

namespace SheafOfModules

open PresheafOfModules CategoryTheory.Presheaf

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- A submodule `N` of (the underlying presheaf of modules of) a sheaf of modules `P` whose
membership is *local* is itself a sheaf of modules: if a section `s` restricts into `N` along a
covering sieve, then `s` already lies in `N`.

This is the general glue between `PresheafOfModules.Submodule` and `SheafOfModules`; the actual
mathematical content of any particular instance is the locality hypothesis `hlocal`. -/
noncomputable def ofLocalSubmodule (P : SheafOfModules.{v} R) (N : P.val.Submodule)
    (hlocal : ∀ ⦃X : Cᵒᵖ⦄ (s : P.val.obj X) (S : Sieve X.unop), S ∈ J X.unop →
      (∀ ⦃Y : C⦄ (f : Y ⟶ X.unop), S f → P.val.map f.op s ∈ N.obj (op Y)) → s ∈ N.obj X) :
    SheafOfModules.{v} R where
  val := N.toPresheafOfModules
  isSheaf := by
    -- The underlying type-valued presheaf of `P`, which is a sheaf.
    have hF : Presieve.IsSheaf J (P.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{v}) :=
      isSheaf_comp_forget P.isSheaf
    -- `N` as a subfunctor of the underlying type-valued presheaf is a sheaf: it is closed under
    -- the topology, which is exactly locality.
    have hG : Presieve.IsSheaf J N.toSubfunctor.toFunctor := by
      rw [N.toSubfunctor.isSheaf_iff hF]
      intro U s hs
      exact hlocal s (N.toSubfunctor.sieveOfSection s) hs fun _ _ hf ↦ hf
    -- Transfer the sheaf condition back to `N.toPresheafOfModules.presheaf`. The forgetful functor
    -- of `AddCommGrpCat` creates (hence reflects) limits at every universe, so no universe
    -- restriction is needed here.
    apply Presheaf.isSheaf_of_isSheaf_comp J (s := CategoryTheory.forget AddCommGrpCat.{v})
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_iso J (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by cat_disch)) hG

end SheafOfModules
