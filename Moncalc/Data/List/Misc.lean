/-
Copyright (c) 2022 Jun Yoshida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace List

universe u

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

end List
