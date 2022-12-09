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
import Moncalc.CategoryTheory.List.Monad
import Moncalc.CategoryTheory.NatTrans

namespace CategoryTheory

universe u

#print Functor.comp
example {α β γ δ : Type _} [Category α] [Category β] [Category γ] [Category δ] (F : Functor α β) (G : Functor β γ) (H : Functor γ δ) : Functor.comp (Functor.comp F G) H = F ⋙ (G ⋙ H) := by
  unfold Functor.comp
  rfl

set_option autoImplicit false

class LaxMonoidal (α : Type u) extends Category α where
  tensor : Functor (List α) α
  unitor : NatTrans (𝟭 α) (List.singletonF ⋙ tensor)
  associator : NatTrans (List.mapF tensor ⋙ tensor) (List.joinF ⋙ tensor)
  -- Two paths `𝟭 _ ⋙ tensor ⟶ tensor` must agree with each other
  coherence_unit_right :
    whiskerRight (NatTrans.ofEq List.mapF_id.symm) tensor
      ≫ whiskerRight (List.mapNT unitor) tensor
      ≫ whiskerRight (NatTrans.ofEq (List.mapF_Fcomp List.singletonF tensor)) tensor
      ≫ whiskerLeft (List.mapF List.singletonF) associator
      ≫ whiskerRight (NatTrans.ofEq (List.joinF_singletonF_right)) tensor
    = NatTrans.id tensor
  --- Two paths `tensor ⋙ 𝟭 _ ⟶ tensor` must agree with each other
  coherence_unit_left :
    whiskerLeft tensor unitor
      ≫ whiskerLeft List.singletonF associator
      ≫ whiskerRight (NatTrans.ofEq List.joinF_singletonF_left) tensor
    = NatTrans.id tensor
  -- Two paths `List.mapF (List.mapF tensor ⋙ tensor) ⋙ tensor ⟶ List.joinF ⋙ List.joinF ⋙ tensor` must agree with each other.
  coherence_assoc :
    whiskerRight (NatTrans.ofEq (List.mapF_Fcomp (List.mapF tensor) tensor)) tensor
      ≫ whiskerLeft (List.mapF (List.mapF tensor)) associator
      ≫ whiskerRight (NatTrans.ofEq (List.comp_joinF_mapF tensor).symm) tensor
      ≫ whiskerLeft List.joinF associator
    =
    whiskerRight (List.mapNT associator) tensor
      ≫ whiskerRight (NatTrans.ofEq (List.mapF_Fcomp List.joinF tensor)) tensor
      ≫ whiskerLeft (List.mapF List.joinF) associator
      ≫ whiskerRight (NatTrans.ofEq (List.joinF_assoc).symm) _

end CategoryTheory