import Algae.GroupTheory.Group

variable {α: Type u}

def DihedralGroup {n: Nat} (hn: 0 < n): Group (Fin n × Fin 2) := {
  unit := (⟨0, hn⟩, ⟨0, Nat.zero_lt_two⟩)
  op := sorry
  identity := by sorry
  assoc := by sorry
  inv := sorry
  inverse := by sorry
}
