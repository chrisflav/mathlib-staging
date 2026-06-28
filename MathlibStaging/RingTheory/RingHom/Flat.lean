/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.RingHom.Flat
public import MathlibStaging.Init

/-!
-/

@[expose] public section

/-- If `M` is an `S`-module that is flat over `S`, and `φ : R →+* S` is a flat ring homomorphism,
then `M` is flat over `R` for the module structure obtained by restricting scalars along `φ`. -/
theorem Module.Flat.trans_compHom {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {M : Type*} [AddCommGroup M] [Module S M] (hφ : RingHom.Flat φ) (hM : Module.Flat S M) :
    letI := Module.compHom M φ; Module.Flat R M := by
  letI := φ.toAlgebra
  letI := Module.compHom M φ
  haveI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  haveI : Module.Flat R S := hφ
  exact Module.Flat.trans R S M

/-- Restricting scalars along a bijective ring homomorphism preserves and reflects flatness. -/
theorem Module.Flat.compHom_bijective_iff {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Bijective φ) {M : Type*} [AddCommGroup M] [Module S M] :
    (letI := Module.compHom M φ; Module.Flat R M) ↔ Module.Flat S M := by
  refine ⟨fun hM ↦ ?_, fun hM ↦ Module.Flat.trans_compHom φ (.of_bijective hφ) hM⟩
  letI := Module.compHom M φ
  let e : R ≃+* S := RingEquiv.ofBijective φ hφ
  have key := Module.Flat.trans_compHom e.symm.toRingHom (.of_bijective e.symm.bijective) hM
  have h : (inferInstanceAs (Module S M)) = Module.compHom M e.symm.toRingHom :=
    Module.ext' _ _ fun s m ↦ (congrArg (· • m) (e.apply_symm_apply s)).symm
  rwa [← h] at key
