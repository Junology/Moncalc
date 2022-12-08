/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Data.List.Basic

namespace List

universe u v w

theorem map_comp {α : Type u} {β : Type v} {γ : Type w} (g : β → γ) (f : α → β) : ∀ {as : List α}, map (g∘ f) as = map g (as.map f) := by
  intro as
  induction as
  case nil => rfl
  case cons a as h_ind =>
    dsimp [map]
    rw [h_ind]

theorem join_append {α : Type u} : ∀ (ass bss : List (List α)), (ass ++ bss).join = ass.join ++ bss.join
| [], bss => rfl
| (as::ass), bss => by
  dsimp [join]
  rw [List.append_assoc, join_append ass bss]

theorem join_join {α : Type u} : ∀ (asss : List (List (List α))), asss.join.join = (asss.map join).join
| [] => rfl
| cons as asss => by
  dsimp [join]
  rw [join_append, join_join asss]

theorem map_join {α : Type u} {β : Type v} (f : α → β) : ∀ {ass : List (List α)}, map f ass.join = join (map (map f) ass)
| [] => rfl
| (as::ass) => by
  dsimp [join]
  rw [map_append, map_join f (ass:=ass)]

end List
