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
import Moncalc.CategoryTheory.List.Functor

/-!
# The 2-monad structure on `(List,List.mapF)`

As shown in the file `CategoryTheory.List.Functor`, the pair `(List,List.mapF)` admits a structure of a 2-endofunctor on the 2-category Cat of (small) categories.
In this file, we further show that it also admits a 2-monad structure consisting of `List.join` on objects and `DVect2.join` on morphisms.

-/
namespace CategoryTheory.List

universe u v w


/-!
## Compatibility of `(List,List.mapF)` and `append`
-/
namespace appendF

variable {α : Type u} [Category α] {β : Type v} [Category β] (F : Functor α β)

/-
@[simp]
protected
theorem naturality_obj {β : Type v} [Category β] (F : Functor α β) : ∀ {as₁ as₂ : List α}, (mapF.obj F).obj (as₁ ++ as₂) = (mapF.obj F).obj as₁ ++ (mapF.obj F).obj as₂ :=
  List.map_append F.obj _ _
-/

protected
def naturatorLax : (as₁ as₂ : List α) → ((mapF.obj F).obj as₁ ++ (mapF.obj F).obj as₂ ⟶ (mapF.obj F).obj (as₁ ++ as₂))
| [], as₂ => 𝟙 ((mapF.obj F).obj as₂)
| (_::as₁), as₂ => DVect2.cons (𝟙 _) (appendF.naturatorLax as₁ as₂)

protected
lemma naturatorLax_naturality {as₁ as₂ bs₁ bs₂ : List α} {fs : as₁ ⟶ bs₁} {gs : as₂ ⟶ bs₂} : ((mapF.obj F).map fs ++ (mapF.obj F).map gs) ≫ appendF.naturatorLax F bs₁ bs₂ = appendF.naturatorLax F as₁ as₂ ≫ (mapF.obj F).map (fs ++ gs) := by
  induction fs
  case nil =>
    dsimp [appendF.naturatorLax]
    rw [Category.comp_id (Y:=(mapF.obj F).obj bs₂)]
    rw [Category.id_comp (X:=(mapF.obj F).obj as₂)]
    rfl
  case cons f fs h_ind =>
    dsimp [appendF.naturatorLax]
    conv =>
      lhs
      rw [DVect2.cons_append, comp_cons]
      rw [Category.comp_id]
    conv =>
      rhs
      rw [DVect2.cons_append]
      dsimp
      rw [Category.id_comp]
    rw [h_ind]

protected
def naturatorOplax : (as₁ as₂ : List α) → ((mapF.obj F).obj (as₁ ++ as₂) ⟶ (mapF.obj F).obj as₁ ++ (mapF.obj F).obj as₂)
| [], as₂ => 𝟙 ((mapF.obj F).obj as₂)
| (_::as₁), as₂ => DVect2.cons (𝟙 _) (appendF.naturatorOplax as₁ as₂)

protected
lemma naturatorOplax_naturality {as₁ as₂ bs₁ bs₂ : List α} {fs : as₁ ⟶ bs₁} {gs : as₂ ⟶ bs₂} : ((mapF.obj F).map (fs ++ gs)) ≫ appendF.naturatorOplax F bs₁ bs₂ = appendF.naturatorOplax F as₁ as₂ ≫ ((mapF.obj F).map fs ++ (mapF.obj F).map gs) := by
  induction fs
  case nil =>
    dsimp [appendF.naturatorOplax]
    rw [Category.comp_id, Category.id_comp]
    rfl
  case cons f fs h_ind =>
    dsimp [appendF.naturatorOplax]
    conv =>
      lhs
      rw [DVect2.cons_append]
      dsimp
      rw [Category.comp_id]
    conv =>
      rhs
      rw [DVect2.cons_append]
      dsimp
      rw [Category.id_comp]
    rw [h_ind]

@[simp]
protected
theorem naturator_lax_oplax (as₁ as₂ : List α) : appendF.naturatorLax F as₁ as₂ ≫ appendF.naturatorOplax F as₁ as₂ = 𝟙 ((mapF.obj F).obj as₁ ++ (mapF.obj F).obj as₂) := by
  induction as₁
  case nil =>
    dsimp [appendF.naturatorLax, appendF.naturatorOplax]
    rw [Category.id_comp (X:=(mapF.obj F).obj as₂)]
    rfl
  case cons a as₁ h_ind =>
    dsimp [appendF.naturatorLax, appendF.naturatorOplax]
    rw [Category.id_comp]
    rw [h_ind]

@[simp]
protected
theorem naturator_oplax_lax (as₁ as₂ : List α) : appendF.naturatorOplax F as₁ as₂ ≫ appendF.naturatorLax F as₁ as₂ = 𝟙 ((mapF.obj F).obj (as₁ ++ as₂)) := by
  induction as₁
  case nil =>
    dsimp [appendF.naturatorLax, appendF.naturatorOplax]
    rw [Category.id_comp]
  case cons a as₁ h_ind =>
    dsimp [appendF.naturatorLax, appendF.naturatorOplax]
    rw [Category.id_comp]
    rw [h_ind]

end appendF


/-!
## `List.joinF` the functorial join
-/

--- The functor `List (List α) ⥤ List α` consisting of `List.join` on objects and `DVect2.join` on morhisms.
def joinF {α : Type u} [Category α] : Functor (List (List α)) (List α) where
  obj := List.join
  map := DVect2.join
  map_id := by
    intro ass
    simp [CategoryStruct.id]
    induction ass
    case nil => rfl
    case cons as ass h_ind =>
      dsimp [List.id, List.join, DVect2.join] at *
      rw [DVect2.fromList_append, h_ind]
      rfl
  map_comp :=
    let rec map_comp_aux {α : Type u} [Category α] : ∀ {ass bss css : List (List α)} (fss : ass ⟶ bss) (gss : bss ⟶ css), Eq (α:=ass.join ⟶ css.join) (DVect2.join (fss ≫ gss)) (fss.join ≫ gss.join)
    | [], [], [], DVect2.nil, DVect2.nil => rfl
    | (_::_), (_::_), (_::_), DVect2.cons _ fss, DVect2.cons _ gss => by
      dsimp [DVect2.join]
      rw [map_comp_aux fss gss, appendF.map_comp]
    map_comp_aux


namespace joinF

@[simp]
protected
theorem obj_cons {α : Type u} [Category α] : ∀ {as : List α} {ass : List (List α)}, (joinF (α:=α)).obj (as::ass) = as ++ (joinF (α:=α)).obj ass := rfl

@[simp]
protected
theorem map_cons {α : Type u} [Category α] : ∀ {as bs : List α} {ass bss : List (List α)} {fs : as ⟶ bs} {fss : ass ⟶ bss}, (joinF (α:=α)).map (DVect2.cons fs fss) = HAppend.hAppend (α:=DVect2 (Quiver.Hom (V:=α)) as bs) (β:=DVect2 (Quiver.Hom (V:=α)) ass.join bss.join) fs ((joinF (α:=α)).map fss) := rfl

/-!
### The naturality of `List.joinF`
-/
section naturality

variable {α : Type u} [Category α] {β : Type v} [Category β] (F : Functor α β)

--- Naturality as an equality
protected
theorem naturality : mapF.obj (mapF.obj F) ⋙ joinF (α:=β) = joinF (α:=α) ⋙ mapF.obj F := by
  apply eqF_List
  . intro ass
    induction ass
    case a.nil => rfl
    case a.cons as ass h_ind =>
      dsimp at *
      have : ∀ (as bs : List α), (mapF.obj F).obj (as++bs) = (mapF.obj F).obj as ++ (mapF.obj F).obj bs :=
        λ as bs => List.map_append F.obj _ _
      rw [this, h_ind]
  . intros as₁ as₂ fs
    induction fs
    case a.nil => exact DVect2.Eq.nil_rfl
    case a.cons f fs h_ind =>
      dsimp
      have : ∀ {as₁ as₂ bs₁ bs₂ : List α} (fs₁ : as₁ ⟶ bs₁) (fs₂ : as₂ ⟶ bs₂), DVect2.Eq ((mapF.obj F).map (fs₁ ++ fs₂)) ((mapF.obj F).map fs₁ ++ (mapF.obj F).map fs₂) :=
        λ fs₁ fs₂ => DVect2.map_append F.obj F.obj F.map
      apply DVect2.Eq.trans _ (this f (joinF.map fs)).symm
      apply DVect2.eq_of_eq_append_eq (DVect2.Eq.of rfl) h_ind

set_option autoImplicit false

protected
def naturatorLax : (ass : List (List α)) → ((joinF (α:=α) ⋙ mapF.obj F).obj ass ⟶ (mapF.obj (mapF.obj F) ⋙ joinF (α:=β)).obj ass)
| [] => DVect2.nil
| (as::ass) =>
  appendF.naturatorOplax F as ((joinF (α:=α)).obj ass) ≫ ((mapF.obj F).map (𝟙 as) ++ joinF.naturatorLax ass)

protected
def naturatorOplax : (ass : List (List α)) → ((mapF.obj (mapF.obj F) ⋙ joinF (α:=β)).obj ass ⟶ (joinF (α:=α) ⋙ mapF.obj F).obj ass)
| [] => DVect2.nil
| (as::ass) => by
  dsimp
  exact ((mapF.obj F).map (𝟙 as) ++ joinF.naturatorOplax ass) ≫ appendF.naturatorLax F as ((joinF (α:=α)).obj ass)

--- Naturality as a natural isomorphism
protected
def naturator : joinF (α:=α) ⋙ mapF.obj F ≅ mapF.obj (mapF.obj F) ⋙ joinF (α:=β) where
  hom := {
    app := joinF.naturatorLax F
    naturality := by
      intro _ _ fss
      induction fss
      case nil => rfl
      case cons fs fss h_ind =>
        dsimp only [joinF.naturatorLax]
        conv =>
          lhs; rw [←Category.assoc]
          change ((mapF.obj F).map (fs ++ joinF.map fss) ≫ appendF.naturatorOplax F _ ((joinF (α:=α)).obj _)) ≫ (Prefunctor.map (Prefunctor.obj mapF.toPrefunctor F).toPrefunctor (𝟙 _) ++ joinF.naturatorLax F _)
          rw [appendF.naturatorOplax_naturality F (fs:=fs)]
          rw [Category.assoc]
          rhs
          rw [appendF.map_comp, (mapF.obj F).map_id, Category.comp_id]
          rhs
          change (joinF ⋙ mapF.obj F).map fss ≫ joinF.naturatorLax F _
          rw [h_ind]
        conv =>
          rhs; rw [Category.assoc]; rhs
          dsimp
          rw [appendF.map_comp, (mapF.obj F).map_id, Category.id_comp]
  }
  inv := {
    app := joinF.naturatorOplax F
    naturality := by
      intro _ _ fss
      induction fss
      case nil => rfl
      case cons fs fss h_ind =>
        dsimp [joinF.naturatorOplax]
        conv =>
          lhs; rw [←Category.assoc, appendF.map_comp, (mapF.obj F).map_id]
          rw [Category.comp_id]
          lhs; rhs
          change (mapF.obj (mapF.obj F) ⋙ joinF).map fss ≫ joinF.naturatorOplax F _
          rw [h_ind]
        conv =>
          rhs; rw [Category.assoc]
          rw [←appendF.naturatorLax_naturality F (fs:=fs)]
          rw [←Category.assoc]
          rw [appendF.map_comp, (mapF.obj F).map_id, Category.id_comp]
  }
  hom_inv_id := by
    ext ass; dsimp
    induction ass
    case nil => rfl
    case cons as ass h_ind =>
      dsimp [joinF.naturatorLax, joinF.naturatorOplax]
      conv =>
        lhs; rw [Category.assoc]; rhs; rw [←Category.assoc]; lhs
        rw [appendF.map_comp, (mapF.obj F).map_id, Category.id_comp]
        rw [h_ind, appendF.map_id]
      rw [Category.id_comp, appendF.naturator_oplax_lax]
  inv_hom_id := by
    ext ass; dsimp
    induction ass
    case nil => rfl
    case cons as ass h_ind =>
      dsimp [joinF.naturatorLax, joinF.naturatorOplax]
      conv =>
        lhs; rw [Category.assoc]; rhs; rw [←Category.assoc]; lhs
        rw [appendF.naturator_lax_oplax]
      rw [Category.id_comp]
      rw [appendF.map_comp, (mapF.obj F).map_id, h_ind, Category.id_comp]
      exact appendF.map_id

end naturality

end joinF

/-!
## `List.singletonF` the embedding of a category `α` into `List α`
-/

--- The functorial embedding of `α` into `List α`.
def singletonF {α : Type u} [Category α] : Functor α (List α) where
  obj := λ a => [a]
  map := λ f => DVect2.cons f DVect2.nil


/-
  2-functoriality and 2-monad laws
-/

theorem whisker_singletonF {α : Type u} [Category α] {β :Type v} [Category β] (F : Functor α β) : F ⋙ singletonF = singletonF ⋙ mapF.obj F := rfl

--- Left unitality of `List` with respect to `joinF` as multiplication and `singletonF` as unit.
theorem joinF_singletonF_left {α : Type u} [Category α] : singletonF (α:=List α) ⋙ joinF = Functor.id (List α) := by
  dsimp [Functor.comp, Functor.id]
  dsimp [singletonF, joinF, DVect2.join]
  apply eqF_List
  . intro as
    dsimp
    exact List.append_nil as
  . intro as bs fs
    dsimp
    exact DVect2.append_nil _

--- Right unitality of `List` with respect to `joinF` as multiplication and `singletonF` as unit.
theorem joinF_singletonF_right {α : Type u} [Category α] : mapF.obj singletonF ⋙ joinF = Functor.id (List α) := by
  dsimp [Functor.comp, Functor.id]
  dsimp [singletonF, joinF, mapF, DVect2.join]
  apply eqF_List <;> dsimp
  . intro as
    induction as
    case a.nil => rfl
    case a.cons a as h_ind => dsimp; rw [h_ind]
  . intro as bs fs
    induction fs
    case a.nil =>
      dsimp [DVect2.map, DVect2.join]
      exact DVect2.Eq.of rfl
    case a.cons a as b bs f fs h_ind =>
      dsimp [DVect2.map, DVect2.join]
      rw [DVect2.cons_append, DVect2.nil_append]
      exact DVect2.Eq.descend rfl h_ind

--- Two different ways to flatten `List (List (List α))` with the `joinF` functor result in (strictly) the same.
theorem joinF_assoc {α : Type u} [Category α] : joinF (α:=List α) ⋙ joinF = mapF.obj joinF ⋙ joinF := by
  dsimp [Functor.comp, joinF, mapF]
  apply eqF_List <;> dsimp
  . intros; exact List.join_join _
  . intros; exact DVect2.join_join _

--- `joinF` is a 2-natural transformation
theorem comp_joinF_mapF {α : Type u} [Category α] {β : Type v} [Category β] (F : Functor α β) : joinF ⋙ mapF.obj F = mapF.obj (mapF.obj F) ⋙ joinF := by
  dsimp [Functor.comp, joinF, mapF]
  apply eqF_List <;> dsimp
  . intro ass
    rw [List.map_join]
  . intros ass₁ ass₂ fss
    induction fss
    case a.nil => exact DVect2.Eq.nil_rfl
    case a.cons fs fss h_ind =>
      dsimp [DVect2.join, DVect2.map]
      apply DVect2.Eq.trans (DVect2.map_append _ _ _)
      apply DVect2.eq_of_eq_append_eq (DVect2.Eq.of rfl)
      exact h_ind

end CategoryTheory.List
