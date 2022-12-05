namespace List

universe u

theorem join_append {α : Type u} : ∀ (ass bss : List (List α)), (ass ++ bss).join = ass.join ++ bss.join
| [], bss => rfl
| (as::ass), bss => by
  dsimp [join]
  rw [List.append_assoc, join_append ass bss]

end List
