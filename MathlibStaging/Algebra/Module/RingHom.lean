/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.RingHom
public import MathlibStaging.Init

/-!
-/

@[expose] public section

variable {R S M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- The scalar action of `Module.compHom M f` (restriction of scalars along a ring
homomorphism `f : S →+* R`) is given by `s • m = f s • m`. -/
lemma Module.compHom_smul [Semiring S] (f : S →+* R) (s : S) (m : M) :
    letI := Module.compHom M f; s • m = f s • m :=
  rfl
