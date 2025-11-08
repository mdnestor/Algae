import Algae.GroupTheory.Group

variable {α: Type u}

open Group

-- The center is the set of elements that commute with every other element

def Magma.center (M: Magma α): Set α :=
  λ z ↦ ∀ m, z + m = m + z

-- The center is a submonoid/subgroup respectively.

theorem Monoid.center_submonoid (M: Monoid α): M.sub M.center := {
  unit_mem := by
    intro a
    calc
      0 + a
      _ = a     := by rw [op_unit_left]
      _ = a + 0 := by rw [op_unit_right]
  op_closed := by
    intro x y hx hy m
    calc
      x + y + m
      _ = x + (y + m) := by rw [op_assoc]
      _ = x + (m + y) := by rw [hy]
      _ = x + m + y   := by rw [op_assoc]
      _ = m + x + y   := by rw [hx]
      _ = m + (x + y) := by rw [op_assoc]
}

theorem Group.center_subgroup (G: Group α): G.sub G.center := {
  unit_mem := G.center_submonoid.unit_mem
  op_closed := G.center_submonoid.op_closed
  inv_closed := by
    intro a h m
    calc
      -a + m
      _ = -a + -(-m) := by rw [inv_inv]
      _ = -(-m + a)  := by rw [inv_op]
      _ = -(a + -m)  := by rw [h]
      _ = -(-m) + -a := by rw [inv_op]
      _ = m + -a     := by rw [inv_inv]
}
