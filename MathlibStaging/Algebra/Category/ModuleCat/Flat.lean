/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.RingTheory.RingHom.Flat
public import MathlibStaging.RingTheory.RingHom.Flat
public import MathlibStaging.Init

/-!
# Flat modules, as a property of objects of `ModuleCat R`

We define `ModuleCat.flat R : ObjectProperty (ModuleCat R)`, the property of objects of
`ModuleCat R` given by `Module.Flat`, show that it is closed under isomorphisms and record its
interaction with restriction of scalars (`ModuleCat.restrictScalars`):

* `ModuleCat.flat_restrictScalars`: restriction of scalars along a flat ring homomorphism
  preserves flatness.
* `ModuleCat.flat_restrictScalars_iff_of_bijective`: restriction of scalars along a bijective
  ring homomorphism preserves and reflects flatness.
* `ModuleCat.flat_restrictScalars_comp_iff`: restricting scalars along a composition agrees with
  successively restricting scalars.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace ModuleCat

variable (R : Type u) [CommRing R]

/-- Flat modules, as a property of objects of `ModuleCat R`. -/
def flat : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ Module.Flat R M

variable {R}

@[simp]
lemma flat_iff (M : ModuleCat.{v} R) : flat R M ↔ Module.Flat R M :=
  Iff.rfl

instance : (flat R).IsClosedUnderIsomorphisms where
  of_iso e hM := (Module.Flat.equiv_iff e.toLinearEquiv).mp hM

section RestrictScalars

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

/-- Restriction of scalars along a flat ring homomorphism preserves flatness. -/
lemma flat_restrictScalars {φ : R →+* S} (hφ : φ.Flat) {M : ModuleCat.{v} S} (hM : flat S M) :
    flat R ((restrictScalars φ).obj M) :=
  Module.Flat.trans_compHom φ hφ hM

/-- Restriction of scalars along a bijective ring homomorphism preserves and reflects
flatness. -/
lemma flat_restrictScalars_iff_of_bijective {φ : R →+* S} (hφ : Function.Bijective φ)
    (M : ModuleCat.{v} S) :
    flat R ((restrictScalars φ).obj M) ↔ flat S M :=
  Module.Flat.compHom_bijective_iff φ hφ

/-- Restricting scalars along a composition of ring homomorphisms is flat if and only if
successively restricting scalars is. -/
lemma flat_restrictScalars_comp_iff (f : R →+* S) (g : S →+* T) (M : ModuleCat.{v} T) :
    flat R ((restrictScalars (g.comp f)).obj M) ↔
      flat R ((restrictScalars f).obj ((restrictScalars g).obj M)) :=
  ObjectProperty.prop_iff_of_iso _ (restrictScalarsComp'App f g (g.comp f) rfl M)

end RestrictScalars

end ModuleCat
