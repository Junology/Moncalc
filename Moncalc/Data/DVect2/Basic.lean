/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Moncalc.Data.List.Misc
import Moncalc.Data.DVect2.Defs

namespace DVect2

universe u u₁ u₂ v

variable {α : Type u₁} {β : Type u₂} {γ : α → β → Type v}

-- Since we are discussing a dependent type, we need the "parameter-heterogeneous" equality instead of the ordinary one.
protected
inductive Eq : {as₁ as₂ : List α} → {bs₁ bs₂ : List β} → DVect2 γ as₁ bs₁ → DVect2 γ as₂ bs₂ → Prop
| nil_rfl : DVect2.Eq DVect2.nil DVect2.nil
| descend : {a : α} → {b : β} → {f₁ f₂ : γ a b} → {as₁ as₂ : List α} → {bs₁ bs₂ : List β} → {fs₁ : DVect2 γ as₁ bs₁} → {fs₂ : DVect2 γ as₂ bs₂} → f₁ = f₂ → DVect2.Eq fs₁ fs₂ → DVect2.Eq (cons f₁ fs₁) (cons f₂ fs₂)

local infix:50 " ≡ " => DVect2.Eq

namespace Eq

--- `DVect2.Eq` implies `Eq` provided that the dependent parameters are (definitionally) same.
protected
theorem eq_of : ∀ {as : List α} {bs : List β} {fs gs : DVect2 γ as bs}, fs ≡ gs → fs = gs
| [], [], DVect2.nil, DVect2.nil, DVect2.Eq.nil_rfl => rfl
| (_::_), (_::_), DVect2.cons _ _, DVect2.cons _ _, DVect2.Eq.descend rfl hfsgs =>
  DVect2.Eq.eq_of hfsgs ▸ rfl

--- `DVect2.Eq` from `Eq`
protected
theorem of : ∀ {as : List α} {bs : List β} {fs gs : DVect2 γ as bs}, fs = gs → fs ≡ gs
| [], [], DVect2.nil, _, rfl => DVect2.Eq.nil_rfl
| (_::_), (_::_), DVect2.cons _ _, _, rfl =>
  DVect2.Eq.descend rfl (Eq.of rfl)

--- `DVect2.Eq` is transitive.
protected
theorem trans : ∀ {as₁ as₂ as₃ : List α} {bs₁ bs₂ bs₃ : List β} {fs₁ : DVect2 γ as₁ bs₁} {fs₂ : DVect2 γ as₂ bs₂} {fs₃ : DVect2 γ as₃ bs₃}, fs₁ ≡ fs₂ → fs₂ ≡ fs₃ → fs₁ ≡ fs₃
| [], [], [], [], [], [], DVect2.nil, DVect2.nil, DVect2.nil, DVect2.Eq.nil_rfl, DVect2.Eq.nil_rfl => DVect2.Eq.nil_rfl
| (_::_), (_::_), (_::_), (_::_), (_::_), (_::_), DVect2.cons _ _, DVect2.cons _ _, DVect2.cons _ _, DVect2.Eq.descend rfl h₁, DVect2.Eq.descend rfl h₂ =>
  DVect2.Eq.descend rfl (DVect2.Eq.trans h₁ h₂)

instance instDVect2EqTrans (as₁ as₂ as₃ : List α) (bs₁ bs₂ bs₃ : List β) : Trans (DVect2.Eq (γ:=γ) (as₁:=as₁) (as₂:=as₂) (bs₁:=bs₁) (bs₂:=bs₂)) (DVect2.Eq (as₁:=as₂) (as₂:=as₃) (bs₁:=bs₂) (bs₂:=bs₃)) (DVect2.Eq (as₁:=as₁) (as₂:=as₃) (bs₁:=bs₁) (bs₂:=bs₃)) :=
  Trans.mk DVect2.Eq.trans

--- `DVect2.Eq` is symmetric
protected
theorem symm : ∀ {as₁ as₂ : List α} {bs₁ bs₂ : List β} {fs₁ : DVect2 γ as₁ bs₁} {fs₂ : DVect2 γ as₂ bs₂}, fs₁ ≡ fs₂ → fs₂ ≡ fs₁
| [], [], [], [], DVect2.nil, DVect2.nil, DVect2.Eq.nil_rfl => DVect2.Eq.nil_rfl
| (_::_), (_::_), (_::_), (_::_), DVect2.cons _ _, DVect2.cons _ _ , DVect2.Eq.descend rfl h =>
  DVect2.Eq.descend rfl h.symm

end Eq

theorem nil_append {as : List α} {bs : List β} (fs : DVect2 γ as bs) : DVect2.nil (γ:=γ) ++ fs = fs :=
  rfl

theorem cons_append {a : α} {b : β} (f : γ a b) {as₁ as₂ : List α} {bs₁ bs₂ : List β} (fs₁ : DVect2 γ as₁ bs₁) (fs₂ : DVect2 γ as₂ bs₂) : DVect2.cons f fs₁ ++ fs₂ = DVect2.cons f (fs₁ ++ fs₂) :=
  rfl

theorem append_nil : ∀ {as : List α} {bs : List β} (fs : DVect2 γ as bs), fs ++ DVect2.nil (γ:=γ) ≡ fs
| [], [], DVect2.nil => DVect2.Eq.nil_rfl
| (_::_), (_::_), DVect2.cons f fs => by
  rw [cons_append]
  exact DVect2.Eq.descend rfl (append_nil fs)

theorem append_assoc : ∀ {as₁ as₂ as₃ : List α} {bs₁ bs₂ bs₃ : List β} (fs₁ : DVect2 γ as₁ bs₁) (fs₂ : DVect2 γ as₂ bs₂) (fs₃ : DVect2 γ as₃ bs₃), fs₁ ++ fs₂ ++ fs₃ ≡ fs₁ ++ (fs₂ ++ fs₃)
| [], _, _, [], _, _, DVect2.nil, fs₂, fs₃ => Eq.of rfl
| (_::_), _, _, (_::_), _, _, DVect2.cons f fs₁, fs₂, fs₃ => by
  have h_ind := append_assoc fs₁ fs₂ fs₃
  dsimp [HAppend.hAppend, DVect2.append] at *
  exact DVect2.Eq.descend rfl h_ind

--- congruence of `DVect2.append` with respect to `DVect2.Eq`.
theorem eq_of_eq_append_eq : ∀ {as₁ as₂ as₁' as₂': List α} {bs₁ bs₂ bs₁' bs₂' : List β} {fs₁ : DVect2 γ as₁ bs₁} {fs₂ : DVect2 γ as₂ bs₂} {fs₁' : DVect2 γ as₁' bs₁'} {fs₂' : DVect2 γ as₂' bs₂'}, fs₁ ≡ fs₁' → fs₂ ≡ fs₂' → fs₁ ++ fs₂ ≡ fs₁' ++ fs₂'
| [], _, [], _, [], _, [], _, DVect2.nil, _, DVect2.nil, _, DVect2.Eq.nil_rfl, hfs₂ =>
  hfs₂
| (_::_), _, (_::_), _, (_::_), _, (_::_), _, DVect2.cons _ _, _, DVect2.cons _ _, _, DVect2.Eq.descend hf hfs₁, hfs₂ =>
  DVect2.Eq.descend hf (eq_of_eq_append_eq hfs₁ hfs₂)

--- `DVect2.join` distributes to `DVect2.append`
theorem join_append : ∀ {ass₁ ass₂ : List (List α)} {bss₁ bss₂ : List (List β)} (fss₁ : DVect2 (DVect2 γ) ass₁ bss₁) (fss₂ : DVect2 (DVect2 γ) ass₂ bss₂), (fss₁ ++ fss₂).join ≡ fss₁.join ++ fss₂.join
| [], ass₂, [], bss₂, DVect2.nil, fss₂ => DVect2.Eq.of rfl
| (_::_), ass₂, (_::_), bss₂, DVect2.cons fs₁ fss₁, fss₂ => by
  have h_ind := join_append fss₁ fss₂
  dsimp [DVect2.join, HAppend.hAppend] at *
  apply DVect2.Eq.trans _ (append_assoc fs₁ fss₁.join fss₂.join).symm
  induction fs₁
  case nil => exact h_ind
  case cons _ _ hfs =>
    exact DVect2.Eq.descend rfl hfs

--- Two different ways to flatten `DVect2 (DVect2 (DVect2 γ))` results in the same.
theorem join_join : ∀ {asss : List (List (List α))} {bsss : List (List (List β))} (fsss : DVect2 (DVect2 (DVect2 γ)) asss bsss), fsss.join.join ≡ (fsss.map List.join List.join DVect2.join).join
| [], [], DVect2.nil => DVect2.Eq.nil_rfl
| (_::_), (_::_), DVect2.cons fs fsss => by
  dsimp [DVect2.join, DVect2.map]
  apply DVect2.Eq.trans (DVect2.join_append fs _) _
  apply eq_of_eq_append_eq (DVect2.Eq.of rfl)
  exact join_join fsss

--- `DVect2.fromList` preserves `append` (or `HAppend.hAppend` more precisely).
theorem fromList_append {α : Type u} {γ : α → α → Type v}: ∀ {as bs : List α} (f : (a : α) → γ a a), fromList γ f (as++bs) = fromList γ f as ++ fromList γ f bs
| [], bs, f => rfl
| (a::as), bs, f => by
  dsimp [fromList]
  rw [cons_append]
  rw [fromList_append (as:=as) (bs:=bs) f]

end DVect2