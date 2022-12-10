/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

import Moncalc.Data.DVect2.Defs
import Moncalc.Data.DVect2.Basic

/-!
# Category structure on `List`

We show that `List α` admits a canonical structure of a category provided `Category α`
-/

namespace CategoryTheory.List

universe u v


/-!
## Definition of the structure
-/
section Category

variable {α : Type u} [Category α]

/--
`Hom [a₁,a₂, ..., aₘ] [b₁,b₂, ..., bₙ]` is defined so that
  - if `m=n`, then it is isomorphic to `Hom a₁ b₁ × Hom a₂ b₂ × ⋯ × Hom aₘ bₙ`;
  - otherwise, it is the empty type.
 -/
 @[reducible]
def Hom : List α → List α → Type _ :=
  DVect2 Quiver.Hom

protected
def id : (as : List α) → Hom as as :=
  DVect2.fromList (γ:=Quiver.Hom) CategoryStruct.id

--- Due to `Mathlib4` convention, `comp f g` applies `f` "before" `g`.
protected
def comp : {as bs cs : List α} → Hom as bs → Hom bs cs → Hom as cs
| [], [], [], DVect2.nil, DVect2.nil => DVect2.nil
| (_::_), (_::_), (_::_), DVect2.cons f fs, DVect2.cons g gs => DVect2.cons (f ≫ g) (List.comp fs gs)

/-!
### Lemmas for recursion
-/
@[simp]
protected
theorem id_nil' : List.id (α:=α) [] = DVect2.nil := rfl

@[simp]
protected
theorem id_cons' : ∀ {a : α} {as : List α}, List.id (a::as) = DVect2.cons (𝟙 a) (List.id as) := rfl

@[simp]
protected
theorem comp_nil' : List.comp (α:=α) DVect2.nil DVect2.nil = DVect2.nil := rfl

@[simp]
protected
theorem comp_cons' : ∀ {a b c : α} {as bs cs : List α} {f : Quiver.Hom a b} {fs : Hom as bs} {g : Quiver.Hom b c} {gs : Hom bs cs}, List.comp (DVect2.cons f fs) (DVect2.cons g gs) = DVect2.cons (f ≫ g) (List.comp fs gs) := by
  intros; rfl

--- Right unitality of the composition in `List α`; see the comment on `comp` function for the composition order.
protected
theorem id_comp : ∀ {as bs : List α} (fs : Hom as bs), List.comp (List.id as) fs = fs
| [], [], DVect2.nil => rfl
| (_::_), (_::_), DVect2.cons f fs => by
  dsimp
  rw [Category.id_comp, List.id_comp fs]

-- The left unitality of the composition in `List α`; see the comments on `comp` function for the composition order.
protected
theorem comp_id : ∀ {as bs : List α} (fs : Hom as bs), List.comp fs (List.id bs) = fs
| [], [], DVect2.nil => rfl
| (_::_), (_::_), DVect2.cons f fs => by
  dsimp
  rw [Category.comp_id, List.comp_id fs]

-- The associativity of the composition in `List α`.
protected
theorem assoc : ∀ {as bs cs ds : List α} (fs : Hom as bs) (gs : Hom bs cs) (hs : Hom cs ds), List.comp (List.comp fs gs) hs = List.comp fs (List.comp gs hs)
| [], [], [], [], DVect2.nil, DVect2.nil, DVect2.nil => rfl
| (_::_), (_::_), (_::_), (_::_), DVect2.cons f fs, DVect2.cons g gs, DVect2.cons h hs => by
  dsimp
  rw [Category.assoc, List.assoc fs gs hs]

-- `List α` is a `Category` provided `α` is.
instance instCategoryList : CategoryTheory.Category (List α) where
  Hom := Hom
  id := List.id
  comp := List.comp
  id_comp := List.id_comp
  comp_id := List.comp_id
  assoc := List.assoc


/-!
### Lemmas for recursion that do not destruct the `CategoryTheory` notations
-/

@[simp]
theorem id_nil : 𝟙 (List.nil (α:=α)) = DVect2.nil := rfl

@[simp]
theorem id_cons : ∀ {a : α} {as : List α}, 𝟙 (a::as) = DVect2.cons (𝟙 a) (𝟙 as) := rfl

attribute [reducible] List.Hom

@[simp]
theorem comp_nil : CategoryStruct.comp (obj:=List α) (X:=[]) (Y:=[]) (Z:=[]) DVect2.nil DVect2.nil = DVect2.nil := rfl

@[simp]
theorem comp_cons : ∀ {a b c : α} {as bs cs : List α} {f : a ⟶ b} {fs : as ⟶ bs} {g : b ⟶ c} {gs : bs ⟶ cs}, CategoryStruct.comp (obj:=List α) (X:=a::as) (Y:=b::bs) (Z:=c::cs) (DVect2.cons f fs) (DVect2.cons g gs) = DVect2.cons (f ≫ g) (fs ≫ gs) := rfl

end Category


/-!
## Functorial `append`/`hAppend`
-/
namespace appendF

/--
  `DVect2.append` enables `Hom as₁ bs₁ → Hom as₂ bs₂ → Hom (as₁++as₂) (bs₁++bs₂)` for `as₁ as₂ bs₁ bs₂ : List α`. 
-/
instance instHAppendHom (α : Type u) [Category α] {as₁ as₂ bs₁ bs₂ : List α} : HAppend (as₁ ⟶ bs₁) (as₂ ⟶ bs₂) ((as₁++as₂) ⟶ (bs₁++bs₂)) :=
  inferInstanceAs $ HAppend (DVect2 (Quiver.Hom (V:=α)) as₁ bs₁) (DVect2 (Quiver.Hom (V:=α)) as₂ bs₂) _

variable {α : Type u} [Category α]

@[simp]
protected
lemma map_cons {a b : α} {as₁ as₂ bs₁ bs₂ : List α} (f : a ⟶ b) (fs₁ : as₁ ⟶ bs₁) (fs₂ : as₂ ⟶ bs₂) : HAppend.hAppend (α:=(a::as₁) ⟶ (b::bs₁)) (DVect2.cons f fs₁) fs₂ = DVect2.cons f (fs₁ ++ fs₂) := rfl

@[simp]
protected
theorem map_id {as bs : List α} : 𝟙 as ++ 𝟙 bs = 𝟙 (as++bs) := by
  induction as
  case nil => rfl
  case cons a as h_ind =>
    dsimp
    rw [DVect2.cons_append, h_ind]

@[simp]
protected
theorem map_comp : ∀ {as₁ as₂ bs₁ bs₂ cs₁ cs₂ : List α} (fs₁ : Hom as₁ bs₁) (fs₂ : Hom as₂ bs₂) (gs₁ : Hom bs₁ cs₁) (gs₂ : Hom bs₂ cs₂), (fs₁ ++ fs₂) ≫ (gs₁ ++ gs₂) = HAppend.hAppend (self:=instHAppendHom α) (fs₁ ≫ gs₁) (fs₂ ≫ gs₂)
| [], _, [], _, [], _, DVect2.nil, _, DVect2.nil, _ => rfl
| (_::_), _, (_::_), _, (_::_), _, DVect2.cons f fs₁, fs₂, DVect2.cons g gs₁, gs₂ => by
  rw [DVect2.cons_append, DVect2.cons_append]
  dsimp
  rw [appendF.map_comp fs₁ _ gs₁ _, DVect2.cons_append]

end appendF


/-!
## Misceleneous lemmas
-/

--- Functional extensionality for functors into `List α`
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

end CategoryTheory.List