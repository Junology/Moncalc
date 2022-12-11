/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.NatIso

-- This should be `Mathlib.CategoryTheory.Whiskering` in future
import Moncalc.CategoryTheory.Whiskering

import Moncalc.CategoryTheory.List.Basic
import Moncalc.CategoryTheory.List.Functor
import Moncalc.CategoryTheory.List.Monad
import Moncalc.CategoryTheory.NatTrans

namespace CategoryTheory

universe u

set_option autoImplicit false

class LaxMonoidal (α : Type u) extends Category α where
  tensor : Functor (List α) α
  unitor : NatTrans (𝟭 α) (List.singletonF ⋙ tensor)
  associator : NatTrans (List.mapF.obj tensor ⋙ tensor) (List.joinF ⋙ tensor)
  -- Two paths `𝟭 _ ⋙ tensor ⟶ tensor` must agree with each other
  coherence_unit_right :
    whiskerRight (List.mapF.unitor.hom) tensor
      ≫ whiskerRight (List.mapF.map unitor) tensor
      ≫ whiskerRight (List.mapF.compositor List.singletonF tensor).inv tensor
      ≫ whiskerLeft (List.mapF.obj List.singletonF) associator
      ≫ whiskerRight List.joinF.unitorRight.inv tensor
    = 𝟙 tensor
  --- Two paths `tensor ⋙ 𝟭 _ ⟶ tensor` must agree with each other
  coherence_unit_left :
    whiskerLeft tensor unitor
      ≫ whiskerLeft List.singletonF associator
      ≫ whiskerRight List.joinF.unitorLeft.inv tensor
    = 𝟙 tensor
  -- Two paths `List.mapF (List.mapF tensor ⋙ tensor) ⋙ tensor ⟶ List.joinF ⋙ List.joinF ⋙ tensor` must agree with each other.
  coherence_assoc :
    whiskerRight (List.mapF.compositor (List.mapF.obj tensor) tensor).inv tensor
      ≫ whiskerLeft (List.mapF.obj (List.mapF.obj tensor)) associator
      ≫ whiskerRight (List.joinF.naturator tensor).inv tensor
      ≫ whiskerLeft List.joinF associator
    =
    whiskerRight (List.mapF.map associator) tensor
      ≫ whiskerRight (List.mapF.compositor List.joinF tensor).inv tensor
      ≫ whiskerLeft (List.mapF.obj List.joinF) associator
      ≫ whiskerRight List.joinF.associator.inv _

class UnbiasedMonoidal (α : Type u) extends Category α where
  tensor : Functor (List α) α
  unitor : 𝟭 α ≅ List.singletonF ⋙ tensor
  associator : List.mapF.obj tensor ⋙ tensor ≅ List.joinF ⋙ tensor
  -- Two paths `𝟭 _ ⋙ tensor ⟶ tensor` must agree with each other
  coherence_unit_right :
    whiskerRight List.mapF.unitor.hom tensor
      ≫ whiskerRight (List.mapF.map unitor.hom) tensor
      ≫ whiskerRight (List.mapF.compositor List.singletonF tensor).inv tensor
      ≫ whiskerLeft (List.mapF.obj List.singletonF) associator.hom
      ≫ whiskerRight List.joinF.unitorRight.inv tensor
    = 𝟙 tensor
  --- Two paths `tensor ⋙ 𝟭 _ ⟶ tensor` must agree with each other
  coherence_unit_left :
    whiskerLeft tensor unitor.hom
      ≫ whiskerLeft List.singletonF associator.hom
      ≫ whiskerRight List.joinF.unitorLeft.inv tensor
    = 𝟙 tensor
  -- Two paths `List.mapF (List.mapF tensor ⋙ tensor) ⋙ tensor ⟶ List.joinF ⋙ List.joinF ⋙ tensor` must agree with each other.
  coherence_assoc :
    whiskerRight (List.mapF.compositor (List.mapF.obj tensor) tensor).inv tensor
      ≫ whiskerLeft (List.mapF.obj (List.mapF.obj tensor)) associator.hom
      ≫ whiskerRight (List.joinF.naturator tensor).inv tensor
      ≫ whiskerLeft List.joinF associator.hom
    =
    whiskerRight (List.mapF.map associator.hom) tensor
      ≫ whiskerRight (List.mapF.compositor List.joinF tensor).inv tensor
      ≫ whiskerLeft (List.mapF.obj List.joinF) associator.hom
      ≫ whiskerRight List.joinF.associator.inv _

instance LaxMonoidalOfUnbiased (α : Type u) [UnbiasedMonoidal α] : LaxMonoidal α where
  tensor := UnbiasedMonoidal.tensor
  unitor := UnbiasedMonoidal.unitor.hom
  associator := UnbiasedMonoidal.associator.hom
  coherence_unit_right := UnbiasedMonoidal.coherence_unit_right
  coherence_unit_left := UnbiasedMonoidal.coherence_unit_left
  coherence_assoc := UnbiasedMonoidal.coherence_assoc

instance instUnbiasedMonoidalList (α : Type u) [Category α] : UnbiasedMonoidal (List α) where
  tensor := List.joinF
  unitor := List.joinF.unitorLeft
  associator := NatIso.ofEq (List.joinF.assoc).symm
  coherence_unit_left := by
    ext ass
    simp [whiskerLeft, whiskerRight, Functor.comp]
    simp [List.joinF, List.singletonF]
    induction ass
    case nil =>
      simp [DVect2.join, List.joinF.unitorLeft, List.joinF.unitorLeftLax]
      sorry
    sorry
  coherence_unit_right := by
    sorry
  coherence_assoc := by
    sorry

end CategoryTheory