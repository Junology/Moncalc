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

namespace CategoryTheory.List

universe u v w

--- The functor `List (List α) ⥤ List α` consisting of `List.join` on objects and `DVect2.join` on morhisms.
def joinF {α : Type u} [Category α] : CategoryTheory.Functor (List (List α)) (List α) where
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
  map_comp := by
    intro ass bss css fss gss
    simp [CategoryStruct.comp]
    rw [comp_join]

--- The functorial embedding of `α` into `List α`.
def singletonF {α : Type u} [Category α] : CategoryTheory.Functor α (List α) where
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
