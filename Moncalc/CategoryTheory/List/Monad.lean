import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

import Moncalc.Data.DVect2.Basic
import Moncalc.CategoryTheory.List.Basic

namespace CategoryTheory.List

universe u v

/-
  2-monad structure on `List` as an endo-functor on Cat
-/

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

def singletonF {α : Type u} [Category α] : CategoryTheory.Functor α (List α) where
  obj := λ a => [a]
  map := λ f => DVect2.cons f DVect2.nil

theorem mapF_comp {α : Type u} [Category α] {β : Type v} [Category β] (Φ : CategoryTheory.Functor α β) : ∀ {as bs cs : List α} (fs : Hom as bs) (gs : Hom bs cs), List.comp (DVect2.map Φ.obj Φ.obj (@Prefunctor.map α _ β _ Φ.toPrefunctor) fs) (DVect2.map Φ.obj Φ.obj (@Prefunctor.map α _ β _ Φ.toPrefunctor) gs) = DVect2.map Φ.obj Φ.obj (@Prefunctor.map α _ β _ Φ.toPrefunctor) (List.comp fs gs)
| [], [], [], DVect2.nil, DVect2.nil => rfl
| (_::_), (_::_), (_::_), DVect2.cons f fs, DVect2.cons g gs => by
  dsimp [DVect2.map, List.comp]
  rw [Φ.map_comp, mapF_comp Φ fs gs]

def mapF {α : Type u} {β : Type v} [Category α] [Category β] (Φ : CategoryTheory.Functor α β) : CategoryTheory.Functor (List α) (List β) where
  obj := List.map Φ.obj
  map := DVect2.map Φ.obj Φ.obj (@Prefunctor.map α _ β _ Φ.toPrefunctor)
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


/-
  2-monad laws
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

theorem joinF_singletonF_right {α : Type u} [Category α] : mapF singletonF ⋙ joinF = Functor.id (List α) := sorry

theorem joinF_assoc {α : Type u} [Category α] : joinF (α:=List α) ⋙ joinF = mapF joinF ⋙ joinF := sorry

end CategoryTheory.List
