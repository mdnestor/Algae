import Algae.Structure
import Algae.Subobject

variable {α: Type u}

-- The center is the set of elements
-- that commute with every other element
def Center (α: Type u) [Magma α]: Set α :=
  λ z ↦ ∀ m, z + m = m + z

theorem Center.submonoid [Monoid α]: Submonoid (Center α) := {
  unit_mem := by
    intro
    rw [add_zero_left, add_zero_right]
  op_closed := by
    intro x y hx hy m
    calc
      x + y + m
      _ = x + (y + m) := by rw [add_assoc]
      _ = x + (m + y) := by rw [hy]
      _ = x + m + y   := by rw [add_assoc]
      _ = m + x + y   := by rw [hx]
      _ = m + (x + y) := by rw [add_assoc]
}

theorem Center.subgroup [Group α]: Subgroup (Center α) := {
  unit_mem := Center.submonoid.unit_mem
  op_closed := Center.submonoid.op_closed
  inv_closed := by
    intro a h m
    calc
      -a + m
      _ = -a + -(-m) := by rw [neg_neg]
      _ = -(-m + a)  := by rw [neg_plus]
      _ = -(a + -m)  := by rw [h]
      _ = -(-m) + -a := by rw [neg_plus]
      _ = m + -a     := by rw [neg_neg]
}
