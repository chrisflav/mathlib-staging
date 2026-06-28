/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import MathlibStaging.Init
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Submodules of presheaves of modules

Given a presheaf of modules `M` over a presheaf of rings `R` and a family of
submodules `N X ≤ M.obj X` that is stable under the restriction maps of `M`,
we construct the corresponding subobject of `M` in the category
`PresheafOfModules R`, together with its inclusion monomorphism.

## Main definitions

* `PresheafOfModules.Submodule M`: a family of submodules of `M`, stable
  under restriction.
* `PresheafOfModules.Submodule.toPresheafOfModules`: the associated
  presheaf of modules.
* `PresheafOfModules.Submodule.ι`: the inclusion into `M`, a monomorphism.

The families of submodules of `M` form a `CompleteLattice`, with all the lattice
operations computed pointwise.

-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- A family of submodules `N X ≤ M.obj X` of a presheaf of modules `M`, stable
under the restriction maps of `M`. This is the data needed to cut out a
subobject of `M` in `PresheafOfModules R`. -/
structure Submodule (M : PresheafOfModules.{v} R) where
  /-- the submodule of `M.obj X` -/
  toSubmodule (X : Cᵒᵖ) : _root_.Submodule (R.obj X) (M.obj X)
  /-- the family is stable under restriction -/
  map_mem ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y) ⦃m : M.obj X⦄ (hm : m ∈ toSubmodule X) :
    M.map f m ∈ toSubmodule Y

set_option backward.isDefEq.respectTransparency false in
/-- The restriction map `M.map f` of a presheaf of modules `M`, bundled as a semilinear map
along the ring map `R.map f`. -/
noncomputable def restrictₛₗ (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    M.obj X →ₛₗ[(R.map f).hom] M.obj Y where
  toFun m := M.map f m
  map_add' := map_add (M.map f).hom
  map_smul' r m := M.map_smul f r m

@[simp]
lemma restrictₛₗ_apply (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : M.obj X) :
    M.restrictₛₗ f m = M.map f m := rfl

namespace Submodule

variable {M : PresheafOfModules.{v} R} (N : M.Submodule)

@[ext]
lemma ext {N₁ N₂ : M.Submodule} (h : ∀ X, N₁.toSubmodule X = N₂.toSubmodule X) :
    N₁ = N₂ := by
  cases N₁; cases N₂; congr 1; ext X : 1; exact h X

set_option backward.isDefEq.respectTransparency false in
/-- The subobject of `M` cut out by the family of submodules `N`, as a presheaf of modules: over
`X` it is the submodule `N.toSubmodule X`, with restriction maps induced by those of `M`. -/
noncomputable def toPresheafOfModules : PresheafOfModules.{v} R where
  obj X := ModuleCat.of (R.obj X) (N.toSubmodule X)
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj Y) (N.toSubmodule Y)))
    { toFun := fun m ↦ ⟨M.map f m.val, N.map_mem f m.property⟩
      map_add' := fun a b ↦ Subtype.ext (map_add (M.map f).hom a.val b.val)
      map_smul' := fun r m ↦ Subtype.ext (M.map_smul f r m.val) }

@[simp]
lemma toPresheafOfModules_obj (X : Cᵒᵖ) :
    (N.toPresheafOfModules).obj X = ModuleCat.of _ (N.toSubmodule X) := rfl

-- `nolint simpNF`: the LHS is in the intended form; the false positive comes from
-- `toPresheafOfModules_obj` rewriting the (irrelevant) type ascription of the argument.
@[simp, nolint simpNF]
lemma toPresheafOfModules_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : N.toSubmodule X) :
    ((N.toPresheafOfModules).map f m).val = M.map f m.val := rfl

/-- The inclusion of the subobject cut out by `N` into `M`. -/
noncomputable def ι : N.toPresheafOfModules ⟶ M :=
  homMk { app := fun X ↦ AddCommGrpCat.ofHom (N.toSubmodule X).subtype.toAddMonoidHom
          naturality := fun {X Y} f ↦ by ext m; rfl }
    (fun X r m ↦ rfl)

-- `nolint simpNF`: as for `toPresheafOfModules_map_apply`, the LHS is in the intended form.
@[simp, nolint simpNF]
lemma ι_app_apply (X : Cᵒᵖ) (m : N.toSubmodule X) : (N.ι).app X m = m.val := rfl

lemma ι_app_injective (X : Cᵒᵖ) : Function.Injective ((N.ι).app X) :=
  Subtype.val_injective

instance : Mono N.ι := mono_of_injective N.ι_app_injective

lemma mem_iff {X : Cᵒᵖ} (m : M.obj X) :
    (∃ n : N.toSubmodule X, (N.ι).app X n = m) ↔ m ∈ N.toSubmodule X :=
  ⟨fun ⟨n, hn⟩ ↦ hn ▸ n.property, fun hm ↦ ⟨⟨m, hm⟩, rfl⟩⟩

section Lattice

instance : PartialOrder M.Submodule :=
  PartialOrder.lift (fun N : M.Submodule ↦ N.toSubmodule) fun _ _ h ↦ ext (congrFun h)

lemma le_iff {N₁ N₂ : M.Submodule} : N₁ ≤ N₂ ↔ ∀ X, N₁.toSubmodule X ≤ N₂.toSubmodule X :=
  Iff.rfl

/-- The family `N` is contained in the preimage of `N` under each restriction map of `M`. -/
lemma le_comap {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    N.toSubmodule X ≤ (N.toSubmodule Y).comap (M.restrictₛₗ f) :=
  fun _ hm ↦ N.map_mem f hm

/-- The families of submodules of a presheaf of modules `M` form a `CompleteLattice`, with
all the lattice operations computed pointwise. -/
instance : CompleteLattice M.Submodule where
  sup F G :=
    { toSubmodule X := F.toSubmodule X ⊔ G.toSubmodule X
      map_mem := fun _ _ f _ hm ↦ sup_le ((F.le_comap f).trans (Submodule.comap_mono le_sup_left))
        ((G.le_comap f).trans (Submodule.comap_mono le_sup_right)) hm }
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ h₁ h₂ X := sup_le (h₁ X) (h₂ X)
  inf F G :=
    { toSubmodule X := F.toSubmodule X ⊓ G.toSubmodule X
      map_mem := fun _ _ f _ hm ↦ le_inf (inf_le_left.trans (F.le_comap f))
        (inf_le_right.trans (G.le_comap f)) hm }
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ h₁ h₂ X := le_inf (h₁ X) (h₂ X)
  sSup s :=
    { toSubmodule X := ⨆ N ∈ s, N.toSubmodule X
      map_mem := fun X Y f _ hm ↦ by
        have h : (⨆ N ∈ s, N.toSubmodule X) ≤
            (⨆ N ∈ s, N.toSubmodule Y).comap (M.restrictₛₗ f) :=
          iSup₂_le fun N hN ↦ (N.le_comap f).trans
            (Submodule.comap_mono (le_iSup₂ (f := fun N (_ : N ∈ s) ↦ N.toSubmodule Y) N hN))
        exact h hm }
  isLUB_sSup s := ⟨fun N hN X ↦ le_iSup₂_of_le N hN le_rfl,
    fun _ hb X ↦ iSup₂_le fun N hN ↦ hb hN X⟩
  sInf s :=
    { toSubmodule X := ⨅ N ∈ s, N.toSubmodule X
      map_mem := fun _ Y f m hm ↦
        (Submodule.mem_iInf (x := (M.map f m : M.obj Y)) _).mpr fun N ↦
          (Submodule.mem_iInf (x := (M.map f m : M.obj Y)) _).mpr fun hN ↦
            N.map_mem f ((Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hm N) hN) }
  isGLB_sInf s := ⟨fun N hN X ↦ iInf₂_le N hN,
    fun _ hb X ↦ le_iInf₂ fun N hN ↦ hb hN X⟩
  bot :=
    { toSubmodule _ := ⊥
      map_mem := fun X Y f _ hm ↦
        (bot_le : (⊥ : _root_.Submodule (R.obj X) (M.obj X)) ≤
          (⊥ : _root_.Submodule (R.obj Y) (M.obj Y)).comap (M.restrictₛₗ f)) hm }
  bot_le _ _ := bot_le
  top :=
    { toSubmodule _ := ⊤
      map_mem := fun _ _ f _ hm ↦ (Submodule.comap_top (M.restrictₛₗ f)).ge hm }
  le_top _ _ := le_top

@[simp]
lemma sup_toSubmodule (N₁ N₂ : M.Submodule) (X : Cᵒᵖ) :
    (N₁ ⊔ N₂).toSubmodule X = N₁.toSubmodule X ⊔ N₂.toSubmodule X := rfl

@[simp]
lemma inf_toSubmodule (N₁ N₂ : M.Submodule) (X : Cᵒᵖ) :
    (N₁ ⊓ N₂).toSubmodule X = N₁.toSubmodule X ⊓ N₂.toSubmodule X := rfl

@[simp]
lemma sSup_toSubmodule (s : Set M.Submodule) (X : Cᵒᵖ) :
    (sSup s).toSubmodule X = ⨆ N ∈ s, N.toSubmodule X := rfl

@[simp]
lemma sInf_toSubmodule (s : Set M.Submodule) (X : Cᵒᵖ) :
    (sInf s).toSubmodule X = ⨅ N ∈ s, N.toSubmodule X := rfl

@[simp]
lemma top_toSubmodule (X : Cᵒᵖ) : (⊤ : M.Submodule).toSubmodule X = ⊤ := rfl

@[simp]
lemma bot_toSubmodule (X : Cᵒᵖ) : (⊥ : M.Submodule).toSubmodule X = ⊥ := rfl

end Lattice

end Submodule

end PresheafOfModules
