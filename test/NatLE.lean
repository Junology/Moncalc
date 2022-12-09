/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Algebra.Group.Defs
import Moncalc.CategoryTheory.Monoidal.Unbiased

/-!
# Unbiased monoical structure on `Nat`

`Nat` becomes an unbiased monoidal category as a poset.
-/

namespace List

variable {α : Type u} [AddMonoid α]

def sum : List α → α :=
  List.foldr (·+·) 0

theorem sum_nil : sum (α:=α) [] = 0 := rfl

theorem sum_cons (a : α) (as : List α) : sum (a::as) = a + sum as := rfl

theorem sum_append (as bs : List α) : (as++bs).sum = as.sum + bs.sum := by
  induction as
  case nil =>
    change sum bs = 0 + sum bs
    rw [AddMonoid.zero_add]
  case cons a as h_ind =>
    dsimp
    change a + sum (as++bs) = a + sum as + sum bs
    rw [h_ind]
    rw [AddSemigroup.add_assoc]

theorem sum_join (ass : List (List α)) : ass.join.sum = (ass.map sum).sum := by
  induction ass
  case nil => rfl
  case cons n ns h_ind =>
    dsimp
    rw [sum_append, sum_cons, h_ind]

end List


inductive LEHom : Nat → Nat → Type
| mk {m n : Nat} : m ≤ n → LEHom m n

namespace LEHom

@[reducible]
protected
def comp {l m n : Nat} : LEHom l m → LEHom m n → LEHom l n
| mk hlm, mk hmn => mk (trans hlm hmn)

protected
def sum : {ms ns : List Nat} → (hs : DVect2 LEHom ms ns) → LEHom ms.sum ns.sum
| [], [], DVect2.nil => mk (Nat.le_refl 0)
| (_::_), (_::_), DVect2.cons (mk h) hs => mk $ by
  simp
  let (mk h_ind) := LEHom.sum hs
  exact Nat.add_le_add h h_ind

end LEHom

open CategoryTheory

instance instCateroyNatWithLE : Category Nat where
  Hom := LEHom
  id n := LEHom.mk (Nat.le_refl n)
  comp := LEHom.comp

def isoOfEq {m n : Nat} (h : m = n) : m ≅ n where
  hom := LEHom.mk (Nat.le_of_eq h)
  inv := LEHom.mk (Nat.le_of_eq h.symm)

instance instUnbiasedMonoidalNatWithLT : UnbiasedMonoidal Nat where
  tensor := {obj := List.sum, map := LEHom.sum}
  unitor := Iso.refl _
  associator := {
    hom := {app:=λ nss => (isoOfEq (List.sum_join nss)).inv}
    inv := {app:=λ nss => (isoOfEq (List.sum_join nss)).hom}
  }
  coherence_unit_left := rfl
  coherence_unit_right := rfl
  coherence_assoc := rfl

