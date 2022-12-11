/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.NatTrans

import Moncalc.Data.DVect2.Basic
import Moncalc.CategoryTheory.List.Basic

/-!
# The 2-functor structure on `List`

As constructed in `CategoryTheory.List.Basic`, `List α` is a `Category` provided so is `α`.
Furthermore, it is actually a 2-functor; i.e. there are the following data:

  - A functor `mapF : Functor α β ⥤ Functor (List α) (List β)`, which is defined in [here](CategoryTheory/List/Basic.lean);
  - A natural isomorphism `mapF.unitor : 𝟭 (List α) ≅ mapF.obj (𝟭 α)`;
  - A natural isomorphism `mapF.compositor : mapF.obj F ⋙ mapF.obj ≅ mapF.obj (F ⋙ G)`.

These are supposed to satisfy the following conditions:

  - `mapF.naturality₂ : ∀ {F₁ F₂ : α → β} {G₁ G₂ : β → γ} (φ : F₁ ⟶ F₂) (ψ : G₁ → G₂), (mapF.map φ ◫ mapF.map ψ) ≫ mapF.compositor F₂ G₂ = mapF.compositor F₁ G₁ ≫ mapF.map (φ ◫ ψ)` as natural transformations `mapF.obj F₁ ⋙ mapF.obj G₁ ⟶ mapF.obj (F₂ ⋙ G₂)`.
  - the coherences for `mapF.unitor` and `mapF.compositor`.
-/

namespace CategoryTheory.List

universe u v w

namespace mapF

/-!
## Unitor

A natural isomorphism `mapF.obj (𝟭 α) ≅ 𝟭 (List α)` that realizes the equality `mapF.obj_id`.
-/
section unitor

variable {α : Type u} [Category α]

--- The body of the unitor in the "lax" functor direction
protected
def unitorLax : (as : List α) → Hom as ((mapF.obj (𝟭 α)).obj as)
| [] => DVect2.nil
| (a::as) => DVect2.cons (𝟙 a) (mapF.unitorLax as)

--- The body of the unitor in the "oplax" functor direction
protected
def unitorOplax : (as : List α) → Hom ((mapF.obj (𝟭 α)).obj as) as
| [] => DVect2.nil
| (a::as) => DVect2.cons (𝟙 a) (mapF.unitorOplax as)

--- The lax unitor is a right inverse to the oplax unitor.
@[simp]
protected
theorem unitor_lax_oplax (as : List α) : mapF.unitorLax as ≫ mapF.unitorOplax as = 𝟙 as := by
  induction as
  case nil => rfl
  case cons a as h_ind =>
    dsimp [mapF.unitorLax, mapF.unitorOplax, List.id, DVect2.fromList]
    rw [h_ind, Category.id_comp]

--- The lax unitor is a left inverse to the oplax unitor.
@[simp]
protected
theorem unitor_oplax_lax (as : List α) : mapF.unitorOplax as ≫ mapF.unitorLax as = 𝟙 ((mapF.obj (𝟭 α)).obj as) := by
  induction as
  case nil => rfl
  case cons a as h_ind =>
    dsimp [mapF.unitorLax, mapF.unitorOplax, List.id, DVect2.fromList]
    rw [h_ind, Category.id_comp]

--- The unitor of the 2-functor `(List, List.mapF)`.
protected
def unitor : 𝟭 (List α) ≅ mapF.obj (𝟭 α) where
  hom := {
    app := mapF.unitorLax
    naturality := by
      intro as bs fs
      induction fs
      case nil => rfl
      case cons f fs h_ind =>
        dsimp [mapF, mapF.unitorLax, DVect2.map] at *
        rw [h_ind, Category.id_comp, Category.comp_id]
  }
  inv := {
    app := mapF.unitorOplax
    naturality := by
      intro as bs fs
      induction fs
      case nil => rfl
      case cons f fs h_ind =>
        dsimp [mapF, mapF.unitorOplax, DVect2.map] at *
        rw [h_ind, Category.id_comp, Category.comp_id]
  }
  hom_inv_id := by ext; intros; simp
  inv_hom_id := by ext; intros; simp

end unitor


/-!
## Compositor

A natural isomorphism `mapF.obj F ⋙ mapF.obj G ≅ mapF.obj (F ⋙ G)` that realizes the equality `mapF.obj_comp`.
-/

section compositor

variable {α : Type u} [Category α] {β : Type v} [Category β] {γ : Type w} [Category γ] (F : Functor α β) (G : Functor β γ)

protected
def compositorLax : (as : List α) → Hom ((mapF.obj F ⋙ mapF.obj G).obj as) ((mapF.obj (F ⋙ G)).obj as)
| [] => DVect2.nil
| (_::as) => DVect2.cons (𝟙 _) (mapF.compositorLax as)

protected
def compositorOplax : (as : List α) → Hom ((mapF.obj (F ⋙ G)).obj as) ((mapF.obj F ⋙ mapF.obj G).obj as)
| [] => DVect2.nil
| (_::as) => DVect2.cons (𝟙 _) (mapF.compositorOplax as)

@[simp]
protected
theorem compositor_lax_oplax (as : List α) : mapF.compositorLax F G as ≫ mapF.compositorOplax F G as = 𝟙 ((mapF.obj F ⋙ mapF.obj G).obj as) := by
  induction as
  case nil => rfl
  case cons a as h_ind =>
    dsimp [mapF.compositorLax, mapF.compositorOplax]
    rw [h_ind, Category.id_comp]
    rfl

@[simp]
protected
theorem compositor_oplax_lax (as : List α) : mapF.compositorOplax F G as ≫ mapF.compositorLax F G as = 𝟙 ((mapF.obj (F ⋙ G)).obj as) := by
  induction as
  case nil => rfl
  case cons a as h_ind =>
  dsimp [mapF.compositorLax, mapF.compositorOplax]
  rw [h_ind, Category.id_comp]

protected
def compositor : mapF.obj F ⋙ mapF.obj G ≅ mapF.obj (F ⋙ G) where
  hom := {
    app := mapF.compositorLax F G
    naturality := by
      intro as bs fs
      induction fs
      case nil => rfl
      case cons f fs h_ind =>
        dsimp [mapF.compositorLax] at *
        rw [h_ind, Category.id_comp, Category.comp_id]
  }
  inv := {
    app := mapF.compositorOplax F G
    naturality := by
      intro as bs fs
      induction fs
      case nil => rfl
      case cons f fs h_ind =>
        dsimp [mapF.compositorOplax]
        rw [h_ind, Category.id_comp, Category.comp_id]
        rfl
  }
  hom_inv_id := by ext; intros; simp
  inv_hom_id := by ext; intros; simp

end compositor


/-!
## Coherences
-/

--- Compatibility of `mapF.compositor` with the horizontal composition `hcomp`.
protected
theorem naturality₂ {α : Type u} [Category α] {β : Type v} [Category β] {γ :Type w} [Category γ] {F₁ F₂ : Functor α β} {G₁ G₂ : Functor β γ} (φ : F₁ ⟶ F₂) (ψ : G₁ ⟶ G₂) : (mapF.map φ ◫ mapF.map ψ) ≫ (mapF.compositor F₂ G₂).hom = (mapF.compositor F₁ G₁).hom ≫ mapF.map (φ ◫ ψ) := by
  ext as
  induction as
  case nil => rfl
  case cons a as h_ind =>
    dsimp [mapF.compositor, mapF.compositorLax] at *
    rw [h_ind, Category.id_comp, Category.comp_id]

--! TO DO: more coherences

end mapF

end CategoryTheory.List
