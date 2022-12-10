/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.NatIso

namespace CategoryTheory

namespace NatTrans

universe u v

protected
def ofEq {α : Type u} [Category α] {β : Type v} [Category β] : ∀ {F G : Functor α β}, F=G → NatTrans F G
| F, _, rfl => NatTrans.id F

end NatTrans

namespace NatIso

protected
def ofEq {α : Type u} [Category α] {β : Type v} [Category β] : ∀ {F G : Functor α β}, F = G → (F ≅ G)
| F, _, rfl => Iso.refl F

end NatIso

end CategoryTheory