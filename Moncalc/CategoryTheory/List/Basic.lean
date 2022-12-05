import Mathlib.CategoryTheory.Category.Basic

import Moncalc.Data.DVect2.Defs
import Moncalc.Data.DVect2.Basic

namespace CategoryTheory.List

universe u v
variable {α : Type u} [CategoryTheory.Category α]

/--
`Hom [a₁,a₂, ..., aₘ] [b₁,b₂, ..., bₙ]` is defined so that
  - if `m=n`, then it is isomorphic to `Hom a₁ b₁ × Hom a₂ b₂ × ⋯ × Hom aₘ bₙ`;
  - otherwise, it is the empty type.
 -/
 @[reducible]
def Hom : List α → (List α) → Type _ :=
  DVect2 Quiver.Hom

@[reducible]
protected
def id : (as : List α) → Hom as as :=
  DVect2.fromList Quiver.Hom CategoryStruct.id

protected
def comp : {as bs cs : List α} → Hom as bs → Hom bs cs → Hom as cs
| [], [], [], DVect2.nil, DVect2.nil => DVect2.nil
| (_::_), (_::_), (_::_), DVect2.cons f fs, DVect2.cons g gs => DVect2.cons (f ≫ g) (List.comp fs gs)

protected
theorem id_comp : ∀ {as bs : List α} (fs : Hom as bs), List.comp (List.id as) fs = fs
| [], [], DVect2.nil => rfl
| (_::_), (_::_), DVect2.cons f fs => by
  dsimp [List.comp]
  rw [Category.id_comp, List.id_comp fs]

protected
theorem comp_id : ∀ {as bs : List α} (fs : Hom as bs), List.comp fs (List.id bs) = fs
| [], [], DVect2.nil => rfl
| (_::_), (_::_), DVect2.cons f fs => by
  dsimp [List.comp]
  rw [Category.comp_id, List.comp_id fs]

protected
theorem assoc : ∀ {as bs cs ds : List α} (fs : Hom as bs) (gs : Hom bs cs) (hs : Hom cs ds), List.comp (List.comp fs gs) hs = List.comp fs (List.comp gs hs)
| [], [], [], [], DVect2.nil, DVect2.nil, DVect2.nil => rfl
| (_::_), (_::_), (_::_), (_::_), DVect2.cons f fs, DVect2.cons g gs, DVect2.cons h hs => by
  dsimp [List.comp]
  rw [Category.assoc, List.assoc fs gs hs]

instance instCategoryList : CategoryTheory.Category (List α) where
  Hom := Hom
  id := List.id
  comp := List.comp
  id_comp := List.id_comp
  comp_id := List.comp_id
  assoc := List.assoc

theorem comp_append : ∀ {as₁ as₂ bs₁ bs₂ cs₁ cs₂: List α} (fs₁ : Hom as₁ bs₁) (fs₂ : Hom as₂ bs₂) (gs₁ : Hom bs₁ cs₁) (gs₂ : Hom bs₂ cs₂), List.comp (fs₁ ++ fs₂) (gs₁ ++ gs₂) = List.comp fs₁ gs₁ ++ List.comp fs₂ gs₂
| [], _, [], _, [], _, DVect2.nil, _, DVect2.nil, _ => rfl
| (_::_), _, (_::_), _, (_::_), _, DVect2.cons _ fs₁, fs₂, DVect2.cons _ gs₁, gs₂ => by
  have h_ind := comp_append fs₁ fs₂ gs₁ gs₂
  rw [DVect2.cons_append]
  dsimp [List.comp, HAppend.hAppend, DVect2.append] at *
  rw [h_ind]

theorem comp_join : ∀ {ass bss css : List (List α)} (fss : Hom ass bss) (gss : Hom bss css), List.comp fss.join gss.join = DVect2.join (List.comp fss gss)
| [], [], [], DVect2.nil, DVect2.nil => rfl
| (_::_), (_::_), (_::_), DVect2.cons _ fss, DVect2.cons _ gss => by
  dsimp [DVect2.join]
  rw [comp_append]
  rw [comp_join fss gss]
  rfl

end CategoryTheory.List