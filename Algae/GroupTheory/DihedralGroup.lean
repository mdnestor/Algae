import Algae.GroupTheory.Group

variable {α: Type u}

def CyclicGroup (n: Nat): Group (Fin (n + 1)) := {
  unit := ⟨0, Nat.zero_lt_succ n⟩
  op := fun a b => a + b
  identity := by
    constructor
    intro a
    simp
    intro a
    simp
  assoc := by
    intro a b c
    simp
    sorry
  inv := sorry
  inverse := sorry
}

def DihedralGroup (n: Nat): Group (Fin (n + 1) × Fin 2) := {
  unit := (⟨0, Nat.zero_lt_succ n⟩, ⟨0, Nat.zero_lt_two⟩)
  op := by sorry
  identity := by sorry
  assoc := by sorry
  inv := by sorry
  inverse := by sorry
}
