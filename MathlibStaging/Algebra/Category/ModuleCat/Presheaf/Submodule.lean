/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import MathlibStaging.Init
public import MathlibStaging.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Submodules of presheaves of modules

Given a presheaf of modules `M` over a presheaf of rings `R` and a family of
submodules `N X` of `M.obj X` that is stable under the restriction maps of `M`,
we construct the corresponding subobject of `M` in the category
`PresheafOfModules R`.

## Main definitions

- `PresheafOfModules.Submodule M`: a family of submodules of `M`, stable
  under restriction.
- `PresheafOfModules.Submodule.toPresheafOfModules`: the associated
  presheaf of modules.

The families of submodules of `M` form a `CompleteLattice`, with all the lattice
operations computed pointwise.

-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- A family of submodules `N X` of `M.obj X`, for a presheaf of modules `M`, stable
under the restriction maps of `M`. This is the data needed to cut out a
subobject of `M` in `PresheafOfModules R`. -/
structure Submodule (M : PresheafOfModules.{v} R) where
  /-- the submodule of `M.obj X` -/
  obj (X : Cᵒᵖ) : _root_.Submodule (R.obj X) (M.obj X)
  /-- the family is stable under restriction -/
  map {X Y : Cᵒᵖ} (f : X ⟶ Y) : obj X ≤ (obj Y).comap (M.restrictₛₗ f)

namespace Submodule

variable {M : PresheafOfModules.{v} R} (N : M.Submodule)

@[ext]
lemma ext {N₁ N₂ : M.Submodule} (h : ∀ X, N₁.obj X = N₂.obj X) :
    N₁ = N₂ := by
  cases N₁; cases N₂; congr 1; ext X : 1; exact h X

set_option backward.isDefEq.respectTransparency false in
/-- The subobject of `M` cut out by the family of submodules `N`, as a presheaf of modules: over
`X` it is the submodule `N.obj X`, with restriction maps induced by those of `M`. -/
noncomputable def toPresheafOfModules : PresheafOfModules.{v} R where
  obj X := ModuleCat.of (R.obj X) (N.obj X)
  map {X Y} f := ModuleCat.ofHom
      (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
        (ModuleCat.of (R.obj Y) (N.obj Y)))
    { toFun := fun m ↦ ⟨M.map f m.val, N.map f m.property⟩
      map_add' := fun a b ↦ Subtype.ext (map_add (M.map f).hom a.val b.val)
      map_smul' := fun r m ↦ Subtype.ext (M.map_smul f r m.val) }

@[simp]
lemma toPresheafOfModules_obj (X : Cᵒᵖ) :
    (N.toPresheafOfModules).obj X = ModuleCat.of _ (N.obj X) := rfl

@[simp]
lemma toPresheafOfModules_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : N.obj X) :
    (dsimp% [toPresheafOfModules_obj] ((N.toPresheafOfModules).map f m).val) = M.map f m.val := rfl

/-- The inclusion of the subobject cut out by `N` into `M`. -/
noncomputable def ι : N.toPresheafOfModules ⟶ M :=
  homMk { app := fun X ↦ AddCommGrpCat.ofHom (N.obj X).subtype.toAddMonoidHom
          naturality := fun {X Y} f ↦ by ext m; rfl }
    (fun X r m ↦ rfl)

@[simp]
lemma ι_app_apply (X : Cᵒᵖ) (m : N.obj X) :
    (dsimp% [toPresheafOfModules_obj] ((N.ι).app X m)) = m.val := rfl

lemma ι_app_injective (X : Cᵒᵖ) : Function.Injective ((N.ι).app X) :=
  Subtype.val_injective

instance : Mono N.ι := mono_of_injective N.ι_app_injective

section Lattice

instance : PartialOrder M.Submodule :=
  PartialOrder.lift (fun N : M.Submodule ↦ N.obj) fun _ _ h ↦ ext (congrFun h)

lemma le_iff {N₁ N₂ : M.Submodule} : N₁ ≤ N₂ ↔ ∀ X, N₁.obj X ≤ N₂.obj X :=
  Iff.rfl

/-- The families of submodules of a presheaf of modules `M` form a `CompleteLattice`, with
all the lattice operations computed pointwise. -/
instance : CompleteLattice M.Submodule where
  sup F G :=
    { obj X := F.obj X ⊔ G.obj X
      map f := sup_le ((F.map f).trans (Submodule.comap_mono le_sup_left))
        ((G.map f).trans (Submodule.comap_mono le_sup_right)) }
  le_sup_left _ _ _ := le_sup_left
  le_sup_right _ _ _ := le_sup_right
  sup_le _ _ _ h₁ h₂ X := sup_le (h₁ X) (h₂ X)
  inf F G :=
    { obj X := F.obj X ⊓ G.obj X
      map f := le_inf (inf_le_left.trans (F.map f)) (inf_le_right.trans (G.map f)) }
  inf_le_left _ _ _ := inf_le_left
  inf_le_right _ _ _ := inf_le_right
  le_inf _ _ _ h₁ h₂ X := le_inf (h₁ X) (h₂ X)
  sSup s :=
    { obj X := ⨆ N ∈ s, N.obj X
      map {_ Y} f := iSup₂_le fun N hN ↦ (N.map f).trans
        (Submodule.comap_mono (le_iSup₂ (f := fun N (_ : N ∈ s) ↦ N.obj Y) N hN)) }
  isLUB_sSup _ := ⟨fun N hN _ ↦ le_iSup₂_of_le N hN le_rfl,
    fun _ hb X ↦ iSup₂_le fun _ hN ↦ hb hN X⟩
  sInf s :=
    { obj X := ⨅ N ∈ s, N.obj X
      map f := fun _ hm ↦ Submodule.mem_comap.mpr <|
        (Submodule.mem_iInf _).mpr fun N ↦ (Submodule.mem_iInf _).mpr fun hN ↦
          Submodule.mem_comap.mp (N.map f ((Submodule.mem_iInf _).mp
            ((Submodule.mem_iInf _).mp hm N) hN)) }
  isGLB_sInf _ := ⟨fun N hN _ ↦ iInf₂_le N hN,
    fun _ hb X ↦ le_iInf₂ fun _ hN ↦ hb hN X⟩
  bot :=
    { obj _ := ⊥
      map _ := bot_le }
  bot_le _ _ := bot_le
  top :=
    { obj _ := ⊤
      map _ := le_top }
  le_top _ _ := le_top

@[simp]
lemma sup_obj (N₁ N₂ : M.Submodule) (X : Cᵒᵖ) :
    (N₁ ⊔ N₂).obj X = N₁.obj X ⊔ N₂.obj X := rfl

@[simp]
lemma inf_obj (N₁ N₂ : M.Submodule) (X : Cᵒᵖ) :
    (N₁ ⊓ N₂).obj X = N₁.obj X ⊓ N₂.obj X := rfl

@[simp]
lemma sSup_obj (s : Set M.Submodule) (X : Cᵒᵖ) :
    (sSup s).obj X = ⨆ N ∈ s, N.obj X := rfl

@[simp]
lemma sInf_obj (s : Set M.Submodule) (X : Cᵒᵖ) :
    (sInf s).obj X = ⨅ N ∈ s, N.obj X := rfl

@[simp]
lemma top_obj (X : Cᵒᵖ) : (⊤ : M.Submodule).obj X = ⊤ := rfl

@[simp]
lemma bot_obj (X : Cᵒᵖ) : (⊥ : M.Submodule).obj X = ⊥ := rfl

end Lattice

end Submodule

end PresheafOfModules
