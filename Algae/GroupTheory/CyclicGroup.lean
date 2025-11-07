import Algae.GroupTheory.Group

variable {α: Type u}

def CyclicGroup {n: ℕ} (hn: 0 < n): Group (Fin n) := {
  unit := ⟨0, hn⟩
  op := λ a b ↦ a + b
  identity := by
    have: NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
    constructor
    apply Fin.zero_add
    apply Fin.add_zero
  assoc := by
    intro a b c
    simp
    sorry
  inv := sorry
  inverse := sorry
}
