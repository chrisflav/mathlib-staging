/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import MathlibStaging.Init
public import MathlibStaging.Algebra.Category.ModuleCat.Presheaf
public import MathlibStaging.Algebra.Module.Submodule.Map
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Subfunctor.Basic

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
- `PresheafOfModules.Submodule.toSubfunctor`: the associated subfunctor of the
  underlying type-valued presheaf.

The families of submodules of `M` form a `CompleteLattice`, with all the lattice
operations computed pointwise.
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-- A family of submodules `N X` of `M.obj X`, for a presheaf of modules `M`, stable
under the restriction maps of `M`. This defines a subobject of `M` in `PresheafOfModules R`. -/
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

@[grind .]
lemma map_mem {X Y : Cᵒᵖ} (f : X ⟶ Y) {x : M.obj X} (hx : x ∈ N.obj X) :
    M.map f x ∈ N.obj Y :=
  N.map f hx

attribute [local simp] LinearMap.restrict_apply ModuleCat.semilinearMapAddEquiv in
set_option backward.isDefEq.respectTransparency false in
/-- The presheaf of modules associated to a submodule. -/
@[simps! obj]
noncomputable def toPresheafOfModules : PresheafOfModules.{v} R where
  obj X := ModuleCat.of (R.obj X) (N.obj X)
  map {X Y} f :=
    ModuleCat.semilinearMapAddEquiv _ _ _ <|
      (M.restrictₛₗ f).restrict (p := N.obj X) (q := N.obj Y) (fun _ hc ↦ N.map_mem _ hc)

@[simp]
lemma toPresheafOfModules_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : N.obj X) :
    dsimp% ((N.toPresheafOfModules).map f m).val = M.map f m.val := by
  rfl

/-- The subfunctor of the underlying type-valued presheaf of `M` cut out by `N`: its sections
over `X` are the elements of `M.obj X` lying in `N.obj X`. -/
def toSubfunctor : Subfunctor (M.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{v}) where
  obj X := {r : M.obj X | r ∈ N.obj X}
  map := fun {_ _} f _ hr ↦ N.map_mem f hr

@[simp]
lemma mem_toSubfunctor_obj {X : Cᵒᵖ} (r : M.obj X) :
    r ∈ N.toSubfunctor.obj X ↔ r ∈ N.obj X := Iff.rfl

/-- The inclusion of the subobject cut out by `N` into `M`. -/
@[simps!]
noncomputable def ι : N.toPresheafOfModules ⟶ M :=
  homMk { app := fun X ↦ AddCommGrpCat.ofHom (N.obj X).subtype.toAddMonoidHom } (by cat_disch)

instance : Mono N.ι := mono_of_injective fun _ ↦ Subtype.val_injective

instance : PartialOrder M.Submodule :=
  PartialOrder.lift _ fun _ _ h ↦ ext (congrFun h)

lemma le_iff {N₁ N₂ : M.Submodule} : N₁ ≤ N₂ ↔ ∀ X, N₁.obj X ≤ N₂.obj X :=
  .rfl

@[simps sup_obj inf_obj sSup_obj sInf_obj top_obj bot_obj]
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
      map f := iSup₂_le fun N hN ↦ (N.map f).trans
        (Submodule.comap_mono (le_iSup₂_of_le N hN le_rfl)) }
  isLUB_sSup _ :=
    ⟨fun N hN _ ↦ le_iSup₂_of_le N hN le_rfl, fun _ hb X ↦ iSup₂_le fun _ hN ↦ hb hN X⟩
  sInf s :=
    { obj X := ⨅ N ∈ s, N.obj X
      map f := by
        simp_rw [Submodule.comap_iInf', le_iInf₂_iff]
        intro N hN
        refine iInf₂_le_of_le _ hN (N.map _) }
  isGLB_sInf _ :=
    ⟨fun N hN _ ↦ iInf₂_le N hN, fun _ hb X ↦ le_iInf₂ fun _ hN ↦ hb hN X⟩
  bot.obj := ⊥
  bot.map _ := bot_le
  bot_le _ _ := bot_le
  top.obj := ⊤
  top.map _ := le_top
  le_top _ _ := le_top

end Submodule

end PresheafOfModules
