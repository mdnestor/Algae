import Algae.Group

variable {α: Type u}

local instance [Magma α]: Add α := ⟨op⟩
local instance [Pointed α]: Zero α := ⟨unit⟩
local instance [Group α]: Neg α := ⟨inv⟩

-- The center is the set of elements
-- that commute with every other element
def Center (α: Type u) [Magma α]: Set α :=
  λ z ↦ ∀ m, z + m = m + z

theorem Center.submonoid [Monoid α]: Submonoid (Center α) := {
  unit_mem := by
    intro
    to_additive
    rw [op_unit_right]
  op_closed := by
    intro x y hx hy m
    to_additive
    calc
      x + y + m
      _ = x + (y + m) := by rw [op_assoc]
      _ = x + (m + y) := by rw [hy]
      _ = x + m + y   := by rw [op_assoc]
      _ = m + x + y   := by rw [hx]
      _ = m + (x + y) := by rw [op_assoc]
}
--      ...
theorem Center.subgroup [Group α]: Subgroup (Center α) := {
  unit_mem := Center.submonoid.unit_mem
  op_closed := Center.submonoid.op_closed
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
