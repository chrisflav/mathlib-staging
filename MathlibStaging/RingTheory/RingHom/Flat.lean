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
  have : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Flat R S := hφ
  exact Module.Flat.trans R S M

/-- If the algebra map `R → S` is bijective, then an `S`-module `M` is flat over `R` (via the tower)
iff it is flat over `S`. -/
theorem Module.Flat.iff_of_bijective_algebraMap {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (hb : Function.Bijective (algebraMap R S)) (M : Type*) [AddCommGroup M]
    [Module R M] [Module S M] [IsScalarTower R S M] :
    Module.Flat R M ↔ Module.Flat S M := by
  let e : R ≃+* S := RingEquiv.ofBijective (algebraMap R S) hb
  refine ⟨fun hM ↦ ?_, fun hM ↦ ?_⟩
  · letI : Algebra S R := e.symm.toRingHom.toAlgebra
    haveI : IsScalarTower S R M := IsScalarTower.of_algebraMap_smul fun s x ↦ by
      have h : (algebraMap R S) (e.symm s) = s := e.apply_symm_apply s
      rw [show algebraMap S R s = e.symm s from rfl, ← algebraMap_smul (A := S) (e.symm s) x, h]
    haveI : Module.Flat S R := RingHom.Flat.of_bijective (f := e.symm.toRingHom) e.symm.bijective
    exact Module.Flat.trans S R M
  · haveI : Module.Flat R S :=
      Module.Flat.of_linearEquiv (LinearEquiv.ofBijective (Algebra.linearMap R S) hb).symm
    exact Module.Flat.trans R S M

/-- Restricting scalars along a bijective ring homomorphism preserves and reflects flatness. -/
theorem Module.Flat.compHom_bijective_iff {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Bijective φ) {M : Type*} [AddCommGroup M] [Module S M] :
    (letI := Module.compHom M φ; Module.Flat R M) ↔ Module.Flat S M := by
  letI := φ.toAlgebra
  letI := Module.compHom M φ
  haveI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact Module.Flat.iff_of_bijective_algebraMap hφ M
