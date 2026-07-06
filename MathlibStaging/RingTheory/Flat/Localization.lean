/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Flat.Localization
public import MathlibStaging.RingTheory.Flat.Stability
public import MathlibStaging.Init

/-!
-/

@[expose] public section

open scoped TensorProduct

/-- Localising an `R`-flat module (which is also a module over an `R`-algebra `S`) at a submonoid
of `S` yields again an `R`-flat module. -/
theorem Module.Flat.localizedModule_base {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    (q : Submonoid S) [Module.Flat R M] :
    Module.Flat R (LocalizedModule q M) := by
  have e : LocalizedModule q M ≃ₗ[R] (Localization q ⊗[S] M) :=
    (LocalizedModule.equivTensorProduct q M).restrictScalars R
  have : Module.Flat S (Localization q) := IsLocalization.flat (Localization q) q
  have : Module.Flat R (Localization q ⊗[S] M) := Module.Flat.tensor_tower (Localization q) M
  exact Module.Flat.of_linearEquiv e

/-- **Local–global flatness over a base, indexed by maximal ideals of `S`.** For an `R`-algebra `S`
and an `S`-module `M`, `M` is flat over `R` iff its localization at every maximal ideal of `S` is
flat over `R`. -/
theorem Module.flat_iff_forall_localizedModule_maximal_of_algebra {R S : Type*} [CommRing R]
    [CommRing S] [Algebra R S] (M : Type*) [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower R S M] :
    Module.Flat R M ↔
      ∀ (q : Ideal S) [q.IsMaximal], Module.Flat R (LocalizedModule q.primeCompl M) := by
  refine ⟨fun _ q _ ↦ Module.Flat.localizedModule_base M q.primeCompl, fun h ↦ ?_⟩
  exact Module.flat_of_isLocalized_maximal S M (fun P _ ↦ LocalizedModule P.primeCompl M)
    (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl M) fun P _ ↦ h P
