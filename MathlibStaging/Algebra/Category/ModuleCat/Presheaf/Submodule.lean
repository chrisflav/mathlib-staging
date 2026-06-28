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

@[simp]
lemma toPresheafOfModules_map_apply {X Y : Cᵒᵖ} (f : X ⟶ Y) (m : N.toSubmodule X) :
    ((N.toPresheafOfModules).map f m).val = M.map f m.val := rfl

/-- The inclusion of the subobject cut out by `N` into `M`. -/
noncomputable def ι : N.toPresheafOfModules ⟶ M :=
  homMk { app := fun X ↦ AddCommGrpCat.ofHom (N.toSubmodule X).subtype.toAddMonoidHom
          naturality := fun {X Y} f ↦ by ext m; rfl }
    (fun X r m ↦ rfl)

@[simp]
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

/-- `M.map f` sends the supremum `⨆ N ∈ s, N.toSubmodule X` into `⨆ N ∈ s, N.toSubmodule Y`,
as every member of the family is stable under restriction. -/
private lemma map_mem_biSup {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : Set M.Submodule) {m : M.obj X}
    (hm : m ∈ ⨆ N ∈ s, N.toSubmodule X) :
    M.map f m ∈ ⨆ N ∈ s, N.toSubmodule Y := by
  induction hm using Submodule.iSup_induction with
  | mem N y hy =>
    induction hy using Submodule.iSup_induction with
    | mem hN z hz =>
      exact Submodule.mem_iSup_of_mem N (Submodule.mem_iSup_of_mem hN (N.map_mem f hz))
    | zero =>
      have h : M.map f (0 : M.obj X) = 0 := map_zero (M.map f).hom
      rw [h]
      exact zero_mem _
    | add a b ha hb =>
      have h : M.map f (a + b) = M.map f a + M.map f b := map_add (M.map f).hom a b
      rw [h]
      exact add_mem ha hb
  | zero =>
    have h : M.map f (0 : M.obj X) = 0 := map_zero (M.map f).hom
    rw [h]
    exact zero_mem _
  | add a b ha hb =>
    have h : M.map f (a + b) = M.map f a + M.map f b := map_add (M.map f).hom a b
    rw [h]
    exact add_mem ha hb

@[simps! top_toSubmodule bot_toSubmodule sup_toSubmodule inf_toSubmodule
  sInf_toSubmodule sSup_toSubmodule]
instance : CompleteLattice M.Submodule where
  sup N₁ N₂ :=
    { toSubmodule X := N₁.toSubmodule X ⊔ N₂.toSubmodule X
      map_mem := by
        intro X Y f m hm
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hm
        have h : M.map f (a + b) = M.map f a + M.map f b := map_add (M.map f).hom a b
        rw [h]
        exact Submodule.add_mem_sup (N₁.map_mem f ha) (N₂.map_mem f hb) }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le _ _ _ h₁ h₂ X := by simp [h₁ X, h₂ X]
  inf N₁ N₂ :=
    { toSubmodule X := N₁.toSubmodule X ⊓ N₂.toSubmodule X
      map_mem := by
        intro X Y f m hm
        exact ⟨N₁.map_mem f hm.1, N₂.map_mem f hm.2⟩ }
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup s :=
    { toSubmodule X := ⨆ N ∈ s, N.toSubmodule X
      map_mem := by
        intro X Y f m hm
        exact map_mem_biSup f s hm }
  isLUB_sSup _ := ⟨fun a ha X ↦ le_iSup₂_of_le a ha le_rfl, fun _ _ _ ↦ by aesop⟩
  sInf s :=
    { toSubmodule X := ⨅ N ∈ s, N.toSubmodule X
      map_mem := by
        intro X Y f m hm
        simp only [Submodule.mem_iInf] at hm ⊢
        exact fun N hN ↦ N.map_mem f (hm N hN) }
  isGLB_sInf _ := ⟨fun _ _ _ _ ↦ by aesop, fun _ _ _ ↦ by aesop⟩
  bot := { toSubmodule _ := ⊥
           map_mem := by
             intro X Y f m hm
             obtain rfl : m = 0 := Submodule.mem_bot.mp hm
             have h : M.map f (0 : M.obj X) = 0 := map_zero (M.map f).hom
             rw [h]
             exact Submodule.zero_mem _ }
  bot_le _ _ := bot_le
  top := { toSubmodule _ := ⊤
           map_mem := by
             intro X Y f m _
             exact Submodule.mem_top }
  le_top _ _ := le_top

end Lattice

end Submodule

end PresheafOfModules
