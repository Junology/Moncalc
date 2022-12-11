/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category

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

--- Functional extensionality for functors into `List α`
theorem eqF_List {β : Type v} [Category β] : (F G : Functor α (List β)) → (∀ (a : α), F.obj a = G.obj a) → (∀ (a₁ a₂ : α) (f : a₁ ⟶ a₂), DVect2.Eq (F.map f) (G.map f)) → F = G
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

end Category


/-!
## Basic list operations as functors

One can obtain a functor from an operation on `List` together with its counterpart on `DVect2`.
-/

/-!
### Functorial `map`
-/

def mapF {α : Type u} [Category α] {β : Type v} [Category β] : Functor α β ⥤ Functor (List α) (List β) where
  obj := λ F => {
    obj := List.map F.obj
    map := DVect2.map F.obj F.obj F.map
    map_id := by
      intro as
      induction as
      case nil => rfl
      case cons a as h_ind =>
        dsimp [DVect2.map] at *
        rw [h_ind, F.map_id]
    map_comp :=
      let rec map_comp_aux : ∀ {as bs cs : List α} (fs : Hom as bs) (gs : Hom bs cs), List.comp (DVect2.map F.obj F.obj F.map fs) (DVect2.map F.obj F.obj F.map gs) = DVect2.map F.obj F.obj F.map (List.comp fs gs)
      | [], [], [], DVect2.nil, DVect2.nil => rfl
      | (_::_), (_::_), (_::_), DVect2.cons f fs, DVect2.cons g gs => by
        dsimp [DVect2.map, List.comp]
        rw [F.map_comp, map_comp_aux fs gs]
      by
        intro fs gs
        simp [CategoryStruct.comp]
        rw [map_comp_aux]
  }
  map := @λ F G φ => {
    app := DVect2.dfromList F.obj G.obj φ.app
    naturality := by
      intros as bs fs
      dsimp [CategoryStruct.comp]
      induction fs <;> dsimp [DVect2.map, List.comp]
      /- case nil has been completed -/
      case cons f fs h_ind =>
        rw [φ.naturality]
        apply congrArg
        exact h_ind
  }
  map_id := λ F => by
    ext as; dsimp
    induction as
    case nil => rfl
    case cons a as h_ind =>
      dsimp [DVect2.dfromList]
      rw [h_ind]
  map_comp := by
    intro F G H φ ψ
    ext as; dsimp
    induction as
    case nil => rfl
    case cons a as h_ind =>
      dsimp [DVect2.dfromList]
      rw [h_ind]

namespace mapF

@[simp]
theorem obj_obj_cons {α : Type u} [Category α] {β : Type v} [Category β] {F : Functor α β} : ∀ {a : α} {as : List α}, (mapF.obj F).obj (a::as) = F.obj a :: (mapF.obj F).obj as := rfl

@[simp]
theorem obj_map_cons {α : Type u} [Category α] {β : Type v} [Category β] {F : Functor α β} : ∀ {a b : α} {as bs : List α} {f : a ⟶ b} {fs : as ⟶ bs}, (mapF.obj F).map (DVect2.cons f fs) = DVect2.cons (F.map f) ((mapF.obj F).map fs) := rfl

@[simp]
theorem map_cons {α : Type u} [Category α] {β : Type v} [Category β] {F G : Functor α β} {φ : F ⟶ G} : ∀ {a : α} {as : List α}, (mapF.map φ).app (a::as) = DVect2.cons (φ.app a) ((mapF.map φ).app as) := rfl

--- `mapF : Functor α α ⟶ Functor (List α) (List α)` preserves the identity functor
@[simp]
protected
theorem obj_id {α : Type u} [Category α] : mapF.obj (𝟭 α) = 𝟭 (List α) := by
  apply eqF_List <;> dsimp [Functor.id]
  . intro as
    change List.map id as = as
    rw [List.map_id]
  . intro as₁ as₂ fs
    change DVect2.Eq (DVect2.map id id id fs) fs
    exact DVect2.map_id

--- `mapF : Functor α β ⟶ Functor (List α) (List β)` respects functor composition
@[simp]
protected
theorem obj_comp {α : Type u} [Category α] {β : Type v} [Category β] {γ : Type w} [Category γ] (F : Functor α β) (G : Functor β γ) : mapF.obj (F ⋙ G) = mapF.obj F ⋙ mapF.obj G := by
  dsimp [Functor.comp, mapF]
  apply eqF_List <;> dsimp
  . intro as
    rw [←List.map_comp G.obj F.obj]
    rfl
  . intro as₁ as₂ fs
    exact DVect2.map_comp

end mapF


/-!
### Functorial `append`
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
## Functorial join
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

end joinF


end CategoryTheory.List