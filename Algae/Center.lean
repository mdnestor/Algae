import Algae.Group
import Algae.Subobject

variable {A: Type u}


-- The center is the set of elements
-- that commute with every other element
def Center (A: Type u) [Add A]: Set A :=
  λ z ↦ ∀ m, z + m = m + z

theorem Center.submonoid [Monoid A]: Submonoid (Center A) := {
  zero_mem := by
    intro
    rw [add_zero_left, add_zero_right]
  add_closed := by
    intro x y hx hy m
    calc
      x + y + m
      _ = x + (y + m) := by rw [add_assoc]
      _ = x + (m + y) := by rw [hy]
      _ = x + m + y   := by rw [add_assoc]
      _ = m + x + y   := by rw [hx]
      _ = m + (x + y) := by rw [add_assoc]
}

theorem Center.subgroup [Group A]: Subgroup (Center A) := {
  zero_mem := Center.submonoid.zero_mem
  add_closed := Center.submonoid.add_closed
  neg_closed := by
    intro a ha m
    sorry
}
