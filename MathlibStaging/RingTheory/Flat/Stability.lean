/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Flat.Stability
public import MathlibStaging.Init

/-!
-/

@[expose] public section

open scoped TensorProduct

namespace Module.Flat

section TensorTower

/-- **Flatness of a tensor product over a tower.** If `A` is a flat `S`-algebra and `M` is a flat
`R`-module (where `R → S → A` is a tower), then `A ⊗[S] M` is a flat `R`-module. -/
theorem tensor_tower {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (A : Type*) [CommRing A] [Algebra S A] [Algebra R A] [IsScalarTower R S A] [Flat S A]
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M] [Flat R M] :
    Flat R (A ⊗[S] M) := by
  rw [iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  let g : M ⊗[R] N →ₗ[S] M ⊗[R] N' := TensorProduct.AlgebraTensorModule.lTensor S M f
  have hg : Function.Injective g := by
    have hcoe : (g : M ⊗[R] N → M ⊗[R] N') = LinearMap.lTensor M f := by ext x; rfl
    rw [hcoe]
    exact lTensor_preserves_injective_linearMap (M := M) f hf
  have hbot : Function.Injective (LinearMap.lTensor A g) :=
    lTensor_preserves_injective_linearMap (M := A) g hg
  let eN := TensorProduct.AlgebraTensorModule.assoc R S S A M N
  let eN' := TensorProduct.AlgebraTensorModule.assoc R S S A M N'
  have hsqL : eN'.toLinearMap.restrictScalars R ∘ₗ LinearMap.lTensor (A ⊗[S] M) f
      = (LinearMap.lTensor A g).restrictScalars R ∘ₗ eN.toLinearMap.restrictScalars R := by
    apply TensorProduct.ext'
    intro w n
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [eN, eN', g, TensorProduct.AlgebraTensorModule.assoc_tmul,
        TensorProduct.AlgebraTensorModule.lTensor_tmul]
    | add a b ha hb => simp [TensorProduct.add_tmul, map_add, ha, hb]
  have hsq : (eN' : _ → _) ∘ LinearMap.lTensor (A ⊗[S] M) f
      = LinearMap.lTensor A g ∘ (eN : _ → _) := by
    simpa using congrArg (fun L : _ →ₗ[R] _ ↦ (L : _ → _)) hsqL
  have hcomp : Function.Injective ((eN' : _ → _) ∘ LinearMap.lTensor (A ⊗[S] M) f) := by
    rw [hsq]; exact hbot.comp eN.injective
  exact hcomp.of_comp

end TensorTower

end Module.Flat
