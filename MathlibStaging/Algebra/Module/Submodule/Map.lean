/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.Submodule.Map
public import MathlibStaging.Init

/-!
# Comapping an infimum of submodules

This file generalizes `Submodule.comap_iInf` to arbitrary semilinear maps, dropping the
`RingHomSurjective` assumption. It is meant to replace `Submodule.comap_iInf` upstream.
-/

@[expose] public section

namespace Submodule

variable {R R₂ M M₂ : Type*}
  [Semiring R] [Semiring R₂] [AddCommMonoid M] [AddCommMonoid M₂] [Module R M] [Module R₂ M₂]
  {σ₁₂ : R →+* R₂}

@[simp]
theorem comap_iInf' {ι : Sort*} (f : M →ₛₗ[σ₁₂] M₂) (p : ι → Submodule R₂ M₂) :
    comap f (⨅ i, p i) = ⨅ i, comap f (p i) := by
  ext
  simp

end Submodule
