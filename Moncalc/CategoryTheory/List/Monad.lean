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

namespace CategoryTheory.List

universe u v w

/-
  2-monad structure on `List` as an endo-functor on Cat
-/

section

--- Auxiliary lemma that for every functor `F : α ⥤ β`, the construction `DVect2.map F.obj F.obj F.map : Hom as₁ as₂ → Hom (map F.obj as₁) (map F.obj as₂)` preserves the composition `List.comp`.
private
theorem mapF_comp {α : Type u} [Category α] {β : Type v} [Category β] (Φ : CategoryTheory.Functor α β) : ∀ {as bs cs : List α} (fs : Hom as bs) (gs : Hom bs cs), List.comp (DVect2.map Φ.obj Φ.obj Φ.map fs) (DVect2.map Φ.obj Φ.obj Φ.map gs) = DVect2.map Φ.obj Φ.obj Φ.map (List.comp fs gs)
| [], [], [], DVect2.nil, DVect2.nil => rfl
| (_::_), (_::_), (_::_), DVect2.cons f fs, DVect2.cons g gs => by
  dsimp [DVect2.map, List.comp]
  rw [Φ.map_comp, mapF_comp Φ fs gs]

--- for a given functor `F : α ⥤ β`, `mapF F : List α ⥤ List β` is the functor consisting of `map F.obj` on objects and `DVect2 F.obj F.obj F.map` on morphisms.
def mapF {α : Type u} {β : Type v} [Category α] [Category β] (Φ : CategoryTheory.Functor α β) : CategoryTheory.Functor (List α) (List β) where
  obj := List.map Φ.obj
  map := DVect2.map Φ.obj Φ.obj Φ.map
  map_id := by
    intro as
    simp [CategoryStruct.id]
    induction as
    case nil => rfl
    case cons a as h_ind =>
      dsimp [List.id, DVect2.map, DVect2.fromList]
      rw [h_ind, Φ.map_id]
  map_comp := by
    intro as bs cs fs gs
    simp [CategoryStruct.comp]
    rw [mapF_comp]

end

--- `mapF : Functor α β → Functor (List α) (List β)` extendsto a functor between the functor categories
def mapNT {α : Type u} {β : Type v} [Category α] [Category β] {F G : α ⥤ β} (φ : NatTrans F G) : NatTrans (mapF F) (mapF G) where
  app := DVect2.dfromList F.obj G.obj φ.app
  naturality := by
    intros as bs fs
    dsimp [CategoryStruct.comp,List.mapF]
    induction fs <;> dsimp [DVect2.map, List.comp]
    /- case nil has been completed -/
    case cons f fs h_ind =>
      rw [φ.naturality]
      apply congrArg
      exact h_ind

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
      dsimp [List.id, List.join, DVect2.join]
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

-- Functional extensionality for functors into `List α`
theorem eqF_List {α : Type u} [Category α] {β : Type v} [Category β] : (F G : Functor α (List β)) → (∀ (a : α), F.obj a = G.obj a) → (∀ (a₁ a₂ : α) (f : a₁ ⟶ a₂), DVect2.Eq (F.map f) (G.map f)) → F = G
| Functor.mk F _ _, Functor.mk G _ _ => by
  cases F with | mk F_obj F_map =>
  cases G with | mk G_obj G_map =>
  intro hobj
  have : F_obj = G_obj := funext hobj
  cases this
  dsimp
  intro hmap
  have : @F_map = @G_map := by
    apply funext; intro a; apply funext; intro b
    apply funext
    intro f
    exact (hmap a b f).eq_of
  cases this
  rfl

--- `mapF : Functor α β → Functor (List α) (List β)` respects functor composition
theorem mapF_Fcomp {α : Type u} [Category α] {β : Type v} [Category β] {γ : Type w} [Category γ] (F : Functor α β) (G : Functor β γ) : mapF (F ⋙ G) = mapF F ⋙ mapF G := by
  dsimp [Functor.comp, mapF]
  apply eqF_List <;> dsimp
  . intro as
    rw [←List.map_comp G.obj F.obj]
    rfl
  . intro as₁ as₂ fs
    exact DVect2.map_comp

--- `mapF : Functor α α → Functor (List α) (List α)` preserves the identity functor
theorem mapF_id {α : Type u} [Category α] : mapF (𝟭 α) = 𝟭 (List α) := by
  apply eqF_List <;> dsimp [Functor.id]
  . intro as
    change List.map id as = as
    rw [List.map_id]
  . intro as₁ as₂ fs
    change DVect2.Eq (DVect2.map id id id fs) fs
    exact DVect2.map_id

--- `mapNT : NatTrans F F → NatTrans (mapF F) (mapF F)` preserves the identity natural transformation
theorem mapNT_id {α : Type u} [Category α] {β : Type v} [Category β] (F : Functor α β) : mapNT (NatTrans.id F) = NatTrans.id (mapF F) := by
  simp [mapNT, NatTrans.id]
  apply funext; intro as
  induction as
  case nil => rfl
  case cons a as h_ind =>
    dsimp [DVect2.dfromList]
    rw [h_ind]
    rfl

--- `mapNT : NatTrans F G → NatTrans (mapF F) (mapF G)` preserves the vertical composition
theorem mapNT_vcomp {α : Type u} [Category α] {β : Type v} [Category β] {F G H : Functor α β} (φ : NatTrans F G) (ψ : NatTrans G H) : mapNT (NatTrans.vcomp φ ψ) = NatTrans.vcomp (mapNT φ) (mapNT ψ) := by
  simp [NatTrans.vcomp, mapNT, List.comp]
  apply funext
  intro as
  induction as
  case nil => rfl
  case cons a as h_ind =>
    dsimp [DVect2.dfromList]
    rw [h_ind]
    rfl

/--
  TODO: state and prove `mapNT_hcomp`.
  As our "associator" `mapF_Fcomp : mapF (F ⋙ G) = mapF F ⋙ mapF G` is only a propositional equality, not the definitional one, we need some tricks even to state it.
-/

theorem whisker_singletonF {α : Type u} [Category α] {β :Type v} [Category β] (F : Functor α β) : F ⋙ singletonF = singletonF ⋙ mapF F := rfl

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
theorem joinF_singletonF_right {α : Type u} [Category α] : mapF singletonF ⋙ joinF = Functor.id (List α) := by
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
theorem joinF_assoc {α : Type u} [Category α] : joinF (α:=List α) ⋙ joinF = mapF joinF ⋙ joinF := by
  dsimp [Functor.comp, joinF, mapF]
  apply eqF_List <;> dsimp
  . intros; exact List.join_join _
  . intros; exact DVect2.join_join _

--- `joinF` is a 2-natural transformation
theorem comp_joinF_mapF {α : Type u} [Category α] {β : Type v} [Category β] (F : Functor α β) : joinF ⋙ mapF F = mapF (mapF F) ⋙ joinF := by
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
