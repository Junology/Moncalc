/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

universe u u₁ u₂ u₃ u₄ v v₁ v₂

inductive DVect2 {α : Type u₁} {β : Type u₂} (γ : α → β → Type v) : List α → List β → Type _
| nil : DVect2 γ [] []
| cons {a : α} {as : List α} {b : β} {bs : List β} : γ a b → DVect2 γ as bs → DVect2 γ (a::as) (b::bs)

namespace DVect2

def map {α₁ : Type u₁} {β₁ : Type u₂} {γ₁ : α₁ → β₁ → Type v₁} {α₂ : Type u₃} {β₂ : Type u₄} {γ₂ : α₂ → β₂ → Type v₂} (f : α₁ → α₂) (g : β₁ → β₂) (h : (a : α₁) → (b : β₁) → γ₁ a b → γ₂ (f a) (g b)) : {as : List α₁} → {bs : List β₁} → DVect2 γ₁ as bs → DVect2 γ₂ (as.map f) (bs.map g)
| [], [], DVect2.nil => DVect2.nil
| (a::_), (b::_), DVect2.cons x xs =>
  DVect2.cons (h a b x) (map f g h xs)

def append {α : Type u₁} {β : Type u₂} {γ : α → β → Type v} : {as₁ as₂ : List α} → {bs₁ bs₂ : List β} → DVect2 γ as₁ bs₁ → DVect2 γ as₂ bs₂ → DVect2 γ (as₁++as₂) (bs₁++bs₂)
| [], as₂, [], bs₂, _, cs₂ => List.nil_append as₂ ▸ List.nil_append bs₂ ▸ cs₂
| (_::_), _, (_::_), _, cons c cs, cs₂ => DVect2.cons c (append cs cs₂)

instance instHAppendDVect2 {α : Type u₁} {β : Type u₂} (γ : α → β → Type v) (as₁ as₂ : List α) (bs₁ bs₂ : List β) : HAppend (DVect2 γ as₁ bs₁) (DVect2 γ as₂ bs₂) (DVect2 γ (as₁++as₂) (bs₁++bs₂)) :=
  HAppend.mk append

def join {α : Type u₁} {β : Type u₂} {γ : α → β → Type v} : {ass : List (List α)} → {bss : List (List β)} → DVect2 (DVect2 γ) ass bss → DVect2 γ ass.join bss.join
| [], [], nil => nil
| (_::_), (_::_), cons cs css => cs ++ join css

def fromList {α : Type u} (γ : α → α → Type v) (f : (a : α) → γ a a) : (as : List α) → DVect2 γ as as
| [] => DVect2.nil
| (a::as) => DVect2.cons (f a) (fromList γ f as)

end DVect2

