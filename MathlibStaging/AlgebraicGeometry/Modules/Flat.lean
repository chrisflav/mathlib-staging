/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import MathlibStaging.Algebra.Module.RingHom
public import MathlibStaging.RingTheory.Flat.Localization
public import MathlibStaging.RingTheory.RingHom.Flat
public import MathlibStaging.Init

/-!
# Flat sheaves of modules

Given a morphism of schemes `f : X ⟶ S` and an `𝒪_X`-module `F`, we say that `F` is
*flat* over `S` (via `f`) if for every point `x ∈ X`, the stalk `F_x` is a flat module over the
local ring `𝒪_{S, f(x)}`, where `𝒪_{S, f(x)}` acts on `F_x` through the local ring homomorphism
`f.stalkMap x : 𝒪_{S, f(x)} ⟶ 𝒪_{X, x}` induced by `f`.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.stalkModule`: the canonical module structure of the local
  ring `𝒪_{X, x}` on the stalk `F_x` of an `𝒪_X`-module `F`.
* `AlgebraicGeometry.Scheme.Modules.FlatAt`: the pointwise flatness condition at a point.
* `AlgebraicGeometry.Scheme.Modules.Flat`: the class asserting flatness, defined as
  `∀ x, FlatAt f F x`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.flat_tilde_iff`: for a commutative ring `R` and an `R`-module
  `M`, the sheaf `M^~` on `Spec R` is flat over `Spec R` (via the identity morphism) if and only if
  `M` is a flat `R`-module.
* `AlgebraicGeometry.Scheme.Modules.flat_tilde_iff_of_algebra`: the same criterion for a ring map
  `f : R ⟶ S` and an `S`-module `M`: the sheaf `M^~` on `Spec S` is flat over `Spec R`
  (via `Spec.map f`) if and only if `M` is flat as an `R`-module.
* `AlgebraicGeometry.Scheme.Modules.Flat.comp`: flatness is preserved under composition with a
  flat morphism of the base.
* `AlgebraicGeometry.Scheme.Modules.flat_comp_isOpenImmersion_iff`: flatness is local on the base.
* `AlgebraicGeometry.Scheme.Modules.flat_iff_forall_openCover`: flatness is local on the source.
-/

@[expose] public noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

namespace Scheme.Modules

/-! ### Flatness of a sheaf of modules -/

/-- The canonical module structure of the local ring `𝒪_{X, x}` (the stalk of the structure
sheaf at `x`) on the stalk `F_x` of an `𝒪_X`-module `F`.

We pin the `PresheafOfModules`-instance explicitly rather than via `inferInstance`: `Stalk.lean`
registers two definitionally-equal `Module (X.presheaf.stalk x) _` instances, and the downstream
germ-level rewrites (e.g. via `PresheafOfModules.germ_smul`) only match against this one. -/
abbrev stalkModule {X : Scheme.{u}} (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x

/-- The pointwise flatness condition at a single point `x ∈ X`: the stalk `F_x` is flat over the
local ring `𝒪_{S, f(x)}`, where the latter acts by restriction of scalars along the stalk map
`f.stalkMap x`. -/
def FlatAt {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X) : Prop :=
  letI := stalkModule F x
  letI : Module (S.presheaf.stalk (f.base x)) (F.presheaf.stalk x) :=
    Module.compHom (F.presheaf.stalk x) (f.stalkMap x).hom
  Module.Flat (S.presheaf.stalk (f.base x)) (F.presheaf.stalk x)

/-- A sheaf of modules `F` on a scheme `X` is *flat* over `S` via a morphism `f : X ⟶ S` if for
every point `x ∈ X`, the stalk `F_x` is flat over the local ring `𝒪_{S, f(x)}` (acting by
restriction of scalars along the stalk map `f.stalkMap x`), i.e. if `FlatAt f F x` holds at every
point. -/
class Flat {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) : Prop where
  flatAt : ∀ x : X, FlatAt f F x

/-- `Flat f F` holds iff the pointwise condition `FlatAt f F x` holds for all `x`. -/
theorem flat_iff_forall_flatAt {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    Flat f F ↔ ∀ x : X, FlatAt f F x :=
  ⟨fun h ↦ h.flatAt, fun h ↦ ⟨h⟩⟩

end Scheme.Modules

namespace Tilde

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R)

/-- The local ring `𝒪_{Spec R, x}` is an `R`-algebra (it is the localization of `R` at the prime
corresponding to `x`). -/
instance instAlgebraStalk (x : PrimeSpectrum.Top R) :
    Algebra R ((Spec R).presheaf.stalk x) :=
  StructureSheaf.stalkAlgebra R x

/-- The local ring `𝒪_{Spec R, x}` is the localization of `R` at the prime `x`. -/
instance instIsLocalizationStalk (x : PrimeSpectrum.Top R) :
    IsLocalization.AtPrime ((Spec R).presheaf.stalk x) x.asIdeal :=
  StructureSheaf.IsLocalization.to_stalk R x

/-- The stalk `(M^~)_x` is a module over the local ring `𝒪_{Spec R, x}`. This re-exposes the
canonical `PresheafOfModules`-instance: typeclass search does not otherwise find it through the
`SheafOfModules.presheaf` projection, so the downstream `IsScalarTower`/flatness statements rely on
it being registered here. -/
instance instModuleStalk (x : PrimeSpectrum.Top R) :
    Module ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) :=
  Scheme.Modules.stalkModule (tilde M) x

/-- The actions of `R` and the local ring `𝒪_{Spec R, x}` on the stalk `(M^~)_x` are compatible. -/
instance instScalarTowerStalk (x : PrimeSpectrum.Top R) :
    IsScalarTower R ((Spec R).presheaf.stalk x) ((tilde M).presheaf.stalk x) :=
  IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl

end Tilde

namespace Scheme.Modules

/-! ### Transitivity and base-locality of flatness

We relate `Flat` to flat morphisms of schemes (`AlgebraicGeometry.Flat`), proving that flatness is
transitive along a flat base change and that flatness is local on the base. -/

/-- The underlying ring homomorphism of the stalk map of a composition factors as the composition
of the underlying ring homomorphisms of the stalk maps. -/
lemma stalkMap_comp_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : X) :
    ((f ≫ g).stalkMap x).hom = (f.stalkMap x).hom.comp (g.stalkMap (f.base x)).hom := by
  rw [Scheme.Hom.stalkMap_comp]
  exact CommRingCat.hom_comp _ _

/-- **Transitivity along a flat base.** If a sheaf of modules `F` on `X` is flat over `Y` via
`f : X ⟶ Y`, and `g : Y ⟶ Z` is a flat morphism of schemes, then `F` is flat over `Z` via the
composite `f ≫ g`. -/
theorem Flat.comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (F : X.Modules)
    [hf : Flat f F] [AlgebraicGeometry.Flat g] : Flat (f ≫ g) F := by
  refine ⟨fun x ↦ ?_⟩
  simp only [FlatAt]
  letI := stalkModule F x
  letI : Module (Y.presheaf.stalk (f.base x)) (F.presheaf.stalk x) :=
    Module.compHom (F.presheaf.stalk x) (f.stalkMap x).hom
  rw [congrArg (Module.compHom (F.presheaf.stalk x)) (stalkMap_comp_hom f g x)]
  exact Module.Flat.trans_compHom (g.stalkMap (f.base x)).hom
    (AlgebraicGeometry.Flat.stalkMap g (f.base x)) (hf.flatAt x)

/-- **Flatness is local on the base.** If `j : V ⟶ S` is an open immersion and `g : X ⟶ V`, then
`F` is flat over `S` via `g ≫ j` if and only if it is flat over `V` via `g`. In other words,
flatness over the base only depends on the base through an open neighbourhood of the image. -/
theorem flat_comp_isOpenImmersion_iff {X V S : Scheme.{u}} (g : X ⟶ V) (j : V ⟶ S)
    [IsOpenImmersion j] (F : X.Modules) :
    Flat (g ≫ j) F ↔ Flat g F := by
  have hbij : ∀ x : X, Function.Bijective (j.stalkMap (g.base x)).hom := fun x ↦
    (ConcreteCategory.isIso_iff_bijective (j.stalkMap (g.base x))).mp inferInstance
  refine ⟨fun h ↦ ⟨fun x ↦ ?_⟩, fun h ↦ ⟨fun x ↦ ?_⟩⟩
  all_goals
    simp only [FlatAt]
    letI := stalkModule F x
    letI : Module (V.presheaf.stalk (g.base x)) (F.presheaf.stalk x) :=
      Module.compHom (F.presheaf.stalk x) (g.stalkMap x).hom
    have hcompHom := congrArg (Module.compHom (F.presheaf.stalk x)) (stalkMap_comp_hom g j x)
  · have hx := h.flatAt x
    simp only [FlatAt] at hx
    rw [hcompHom] at hx
    exact (Module.Flat.compHom_bijective_iff (j.stalkMap (g.base x)).hom (hbij x)).1 hx
  · rw [hcompHom]
    exact Module.Flat.trans_compHom (j.stalkMap (g.base x)).hom
      (RingHom.Flat.of_bijective (hbij x)) (h.flatAt x)

/-! ### The affine criterion for an `R`-algebra `S` and an `S`-module `M`

We generalise `flat_tilde_iff` from the identity morphism on `Spec R` to the morphism
`Spec S ⟶ Spec R` induced by an `R`-algebra `S`, applied to the sheaf `M^~` of an `S`-module `M`
(which is in particular an `R`-module). The result: `M^~` is flat over `Spec R` iff `M` is flat as
an `R`-module. -/

/-- The pointwise flatness condition for `M^~` (with `M` an `S`-module, for a ring map `f : R ⟶ S`)
over `Spec R` at a prime `x` of `S` is equivalent to the localization `M_x` being flat over `R`
(with `R` acting on `M` by restriction of scalars along `f`). -/
theorem flatAt_tilde_algebra_iff {R S : CommRingCat.{u}} (f : R ⟶ S) (M : ModuleCat.{u} S)
    (x : PrimeSpectrum S) :
    letI := f.hom.toAlgebra
    letI : Module R M := Module.compHom M f.hom
    letI : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    FlatAt (Spec.map f) (tilde M) x ↔
      Module.Flat R (LocalizedModule x.asIdeal.primeCompl M) := by
  letI := f.hom.toAlgebra
  letI : Module R M := Module.compHom M f.hom
  have : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module ((Spec R).presheaf.stalk ((Spec.map f).base x)) ((tilde M).presheaf.stalk x) :=
    Module.compHom ((tilde M).presheaf.stalk x) ((Spec.map f).stalkMap x).hom
  letI : Module R ((tilde M).presheaf.stalk x) :=
    Module.compHom ((tilde M).presheaf.stalk x) f.hom
  have hsquare : ∀ r : R, ((Spec.map f).stalkMap x).hom
        (algebraMap R ((Spec R).presheaf.stalk ((Spec.map f).base x)) r)
      = algebraMap S ((Spec S).presheaf.stalk x) (f.hom r) := fun r ↦
    AlgebraicGeometry.stalkMap_toStalk_apply f x r
  have : IsScalarTower R S ((tilde M).presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower R ((Spec R).presheaf.stalk ((Spec.map f).base x))
      ((tilde M).presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_smul fun r n ↦ ?_
    rw [Module.compHom_smul, hsquare r, Module.compHom_smul, algebraMap_smul]
  simp only [FlatAt]
  rw [Module.flat_iff_of_isLocalization ((Spec R).presheaf.stalk ((Spec.map f).base x))
      ((Spec.map f).base x).asIdeal.primeCompl ((tilde M).presheaf.stalk x)]
  exact Module.Flat.equiv_iff
    ((IsLocalizedModule.linearEquiv x.asIdeal.primeCompl (tilde.toStalk M x).hom
      (LocalizedModule.mkLinearMap x.asIdeal.primeCompl M)).restrictScalars R)

/-- **The affine case for an `R`-algebra `S`.** For a ring map `f : R ⟶ S` (an `R`-algebra `S`) and
an `S`-module `M` (hence also an `R`-module, by restriction of scalars), the sheaf `M^~` on `Spec S`
is flat over `Spec R` (via `Spec.map f`) if and only if `M` is a flat `R`-module. -/
theorem flat_tilde_iff_of_algebra {R S : CommRingCat.{u}} (f : R ⟶ S) (M : ModuleCat.{u} S) :
    letI := f.hom.toAlgebra
    letI : Module R M := Module.compHom M f.hom
    Flat (Spec.map f) (tilde M) ↔ Module.Flat R M := by
  letI := f.hom.toAlgebra
  letI : Module R M := Module.compHom M f.hom
  have : IsScalarTower R S M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  rw [flat_iff_forall_flatAt]
  refine ⟨fun h ↦ (Module.flat_iff_forall_localizedModule_maximal_of_algebra (R := R) (S := S)
      (M := M)).mpr fun q _ ↦ (flatAt_tilde_algebra_iff f M ⟨q, inferInstance⟩).mp
        (h ⟨q, inferInstance⟩),
    fun hM x ↦ (flatAt_tilde_algebra_iff f M x).mpr
      (Module.Flat.localizedModule_base M x.asIdeal.primeCompl)⟩

/-- **The affine case.** For a commutative ring `R` and an `R`-module `M`, the quasi-coherent
sheaf `M^~` on `Spec R` is flat over `Spec R` (via the identity morphism) if and only if `M` is a
flat `R`-module. This is the special case of `flat_tilde_iff_of_algebra` for the identity ring
map `𝟙 R`. -/
theorem flat_tilde_iff {R : CommRingCat.{u}} (M : ModuleCat.{u} R) :
    Flat (𝟙 (Spec R)) (tilde M) ↔ Module.Flat R M := by
  rw [← Spec.map_id R]
  exact flat_tilde_iff_of_algebra (𝟙 R) M

/-! ### Flatness is local on the source (open covers)

We show that flatness can be checked on the members of an open cover of the source: for an open
cover `{Uᵢ}` of `X`, the module `F` is flat over `S` (via `f : X ⟶ S`) iff each restriction
`F|_{Uᵢ}` is flat over `S` (via `Uᵢ ⟶ X ⟶ S`). -/

-- The `rw`s below rewrite scalar actions on stalks whose module instance enters the goal as a
-- `letI`-bound local instance, while `PresheafOfModules.germ_smul` phrases the action through the
-- canonical instance. These are defeq but not syntactically equal, so `rw` needs the relaxed defeq.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The additive isomorphism `(F.restrict ι)_u ≅ F_{ι u}` coming from `restrictStalkNatIso` is
semilinear over the (iso) stalk map `ι.stalkMap u : 𝒪_{X,ι u} ⟶ 𝒪_{U,u}`: scaling by
`ι.stalkMap u c` on the restriction side corresponds to scaling by `c` on `F`. -/
theorem restrictStalkNatIso_hom_smul {U X : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]
    (F : X.Modules) (u : U) (c : X.presheaf.stalk (ι.base u))
    (m : (F.restrict ι).presheaf.stalk u) :
    letI := stalkModule (F.restrict ι) u
    letI := stalkModule F (ι.base u)
    let Φ : (F.restrict ι).presheaf.stalk u → F.presheaf.stalk (ι.base u) :=
      fun z ↦ (Scheme.Modules.restrictStalkNatIso ι u).hom.app F z
    Φ ((ι.stalkMap u).hom c • m) = c • Φ m := by
  letI := stalkModule (F.restrict ι) u
  letI := stalkModule F (ι.base u)
  intro Φ
  obtain ⟨V, hV, t, rfl⟩ := X.presheaf.exists_germ_eq c
  obtain ⟨W, hW, s, rfl⟩ := (F.restrict ι).presheaf.exists_germ_eq m
  rw [Scheme.Hom.germ_stalkMap_apply ι V u hV t]
  set W' : U.Opens := W ⊓ ι ⁻¹ᵁ V with hW'def
  have huW' : u ∈ W' := ⟨hW, hV⟩
  rw [← TopCat.Presheaf.germ_res_apply U.presheaf (homOfLE inf_le_right : W' ⟶ ι ⁻¹ᵁ V) u huW'
        (ι.app V t),
      ← TopCat.Presheaf.germ_res_apply (F.restrict ι).presheaf (homOfLE inf_le_left : W' ⟶ W) u
        huW' s]
  -- combine the `𝒪_U`-side scalar action into a single germ of a section
  have lemL : U.presheaf.germ W' u huW' (U.presheaf.map (homOfLE inf_le_right).op (ι.app V t))
      • (F.restrict ι).presheaf.germ W' u huW'
        ((F.restrict ι).presheaf.map (homOfLE inf_le_left).op s)
      = (F.restrict ι).presheaf.germ W' u huW'
        (U.presheaf.map (homOfLE inf_le_right).op (ι.app V t)
          • (F.restrict ι).presheaf.map (homOfLE inf_le_left).op s) :=
    (PresheafOfModules.germ_smul (R := U.presheaf) (F.restrict ι).val u W' huW' _ _).symm
  rw [lemL]
  -- push `Φ` through germs of the restricted module
  have hΦ : ∀ (A : U.Opens) (h : u ∈ A) (z : Γ(F.restrict ι, A)),
      Φ ((F.restrict ι).presheaf.germ A u h z)
        = F.presheaf.germ (ι ''ᵁ A) (ι.base u) ⟨u, h, rfl⟩ z := by
    intro A h z
    exact DFunLike.congr_fun (congrArg ConcreteCategory.hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app ι u F h)) z
  rw [hΦ, hΦ, Scheme.Modules.restrict_map]
  -- align the `𝒪_X`-germ of `t` over `ι ''ᵁ W'` and combine the `F`-side action
  have hsub : ι ''ᵁ W' ≤ V := by
    rintro _ ⟨p, hp, rfl⟩
    exact hp.2
  rw [← TopCat.Presheaf.germ_res_apply X.presheaf (homOfLE hsub : ι ''ᵁ W' ⟶ V) (ι.base u)
        ⟨u, huW', rfl⟩ t]
  have lemR : X.presheaf.germ (ι ''ᵁ W') (ι.base u) ⟨u, huW', rfl⟩
        (X.presheaf.map (homOfLE hsub).op t)
      • F.presheaf.germ (ι ''ᵁ W') (ι.base u) ⟨u, huW', rfl⟩
        (F.presheaf.map (ι.opensFunctor.map (homOfLE inf_le_left)).op s)
      = F.presheaf.germ (ι ''ᵁ W') (ι.base u) ⟨u, huW', rfl⟩
        (X.presheaf.map (homOfLE hsub).op t
          • F.presheaf.map (ι.opensFunctor.map (homOfLE inf_le_left)).op s) :=
    (PresheafOfModules.germ_smul (R := X.presheaf) F.val (ι.base u) (ι ''ᵁ W') ⟨u, huW', rfl⟩
      _ _).symm
  -- the structure-sheaf identity comparing the two scalars
  have F2 : (ι.appIso W').inv
        (U.presheaf.map (homOfLE (inf_le_right : W' ≤ ι ⁻¹ᵁ V)).op (ι.app V t))
      = X.presheaf.map (homOfLE hsub).op t := by
    have F2mor : ι.app V ≫ U.presheaf.map (homOfLE (inf_le_right : W' ≤ ι ⁻¹ᵁ V)).op
          ≫ (ι.appIso W').inv = X.presheaf.map (homOfLE hsub).op := by
      rw [Scheme.Hom.appIso_inv_naturality, Scheme.Hom.app_appIso_inv_assoc, ← Functor.map_comp]
      rfl
    rw [← F2mor]
    rfl
  -- conclude: both germs are of the same section of `F`, using the scalar identity `F2`
  refine Eq.trans (congrArg _ ?_) lemR.symm
  exact congrArg
    (· • F.presheaf.map (ι.opensFunctor.map (homOfLE (inf_le_left : W ⊓ ι ⁻¹ᵁ V ≤ W))).op s) F2

/-- **Pointwise comparison under restriction to an open subscheme.** For an open immersion
`ι : U ⟶ X`, the flatness of the restricted module `F|_U` at `u` (over `S`, via `ι ≫ f`) is
equivalent to the flatness of `F` at `ι(u)`. This holds because the stalk map of an open immersion
is an isomorphism, so restriction does not change the stalk data. -/
theorem flatAt_restrict_iff {U X S : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]
    (f : X ⟶ S) (F : X.Modules) (u : U) :
    FlatAt (ι ≫ f) (F.restrict ι) u ↔ FlatAt f F (ι.base u) := by
  letI := stalkModule (F.restrict ι) u
  letI := stalkModule F (ι.base u)
  let Φe : (F.restrict ι).presheaf.stalk u ≃+ F.presheaf.stalk (ι.base u) :=
    ((Scheme.Modules.restrictStalkNatIso ι u).app F).addCommGroupIsoToAddEquiv
  -- The two stalk-map base points `(ι ≫ f) u` and `f (ι u)` only agree up to
  -- `Scheme.Hom.comp_base`; we phrase the module structures over the former (matching the
  -- left-hand `FlatAt` syntactically), letting `f.stalkMap (ι.base u)` act through the latter.
  letI : Module (S.presheaf.stalk ((ι ≫ f).base u)) ((F.restrict ι).presheaf.stalk u) :=
    Module.compHom ((F.restrict ι).presheaf.stalk u) ((ι ≫ f).stalkMap u).hom
  letI : Module (S.presheaf.stalk ((ι ≫ f).base u)) (F.presheaf.stalk (ι.base u)) :=
    Module.compHom (F.presheaf.stalk (ι.base u)) (f.stalkMap (ι.base u)).hom
  let e : (F.restrict ι).presheaf.stalk u ≃ₗ[S.presheaf.stalk ((ι ≫ f).base u)]
      F.presheaf.stalk (ι.base u) :=
    Φe.toLinearEquiv (by
      intro b m
      have hb : ((ι ≫ f).stalkMap u).hom b
          = (ι.stalkMap u).hom ((f.stalkMap (ι.base u)).hom b) := by
        rw [stalkMap_comp_hom ι f u]
        rfl
      have key := restrictStalkNatIso_hom_smul ι F u ((f.stalkMap (ι.base u)).hom b) m
      rw [← hb] at key
      exact key)
  exact Module.Flat.equiv_iff e

/-- Flatness of the restriction of `F` to an open subscheme `U` (via `ι ≫ f`) is equivalent to the
pointwise flatness of `F` at every point of `U`. -/
theorem flat_restrict_iff {U X S : Scheme.{u}} (ι : U ⟶ X) [IsOpenImmersion ι]
    (f : X ⟶ S) (F : X.Modules) :
    Flat (ι ≫ f) (F.restrict ι) ↔ ∀ u : U, FlatAt f F (ι.base u) := by
  rw [flat_iff_forall_flatAt]
  exact forall_congr' fun u ↦ flatAt_restrict_iff ι f F u

/-- **Flatness is local on the source.** For an open cover `𝒰` of `X`, the module `F` is flat over
`S` (via `f`) if and only if for every member `Uᵢ` of the cover, the restriction `F|_{Uᵢ}` is flat
over `S` (via `𝒰.f i ≫ f`). -/
theorem flat_iff_forall_openCover {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules)
    (𝒰 : X.OpenCover) :
    Flat f F ↔ ∀ i, Flat (𝒰.f i ≫ f) (F.restrict (𝒰.f i)) := by
  simp_rw [flat_restrict_iff, flat_iff_forall_flatAt]
  refine ⟨fun h i u ↦ h _, fun h x ↦ ?_⟩
  obtain ⟨u, hu⟩ := 𝒰.covers x
  rw [← hu]
  exact h (𝒰.idx x) u

end Scheme.Modules

end AlgebraicGeometry
