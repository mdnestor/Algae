import Algae.Group

variable {R: Type u}


class Ring (α: Type u) where
  add_struct: CommGroup α
  mul_struct: Monoid α
  distrib: Distributive mul_struct.op add_struct.op

def Ring.add [Ring α]: α → α → α :=
  Ring.add_struct.op

def Ring.mul [Ring α]: α → α → α :=
  Ring.mul_struct.op

def Ring.zero [Ring α]: α :=
  Ring.add_struct.unit

def Ring.one [Ring α]: α :=
  Ring.mul_struct.unit

def Ring.neg [Ring α]: α → α :=
  Ring.add_struct.inv

def Ring.sub [Ring α]: α → α → α :=
  λ a b ↦ add a (neg b)

instance [Ring α]: Add α := {
  add := Ring.add
}

instance [Ring α]: Mul α := {
  mul := Ring.mul
}

instance [Ring α]: Zero α := {
  zero := Ring.add_struct.unit
}

instance [Ring α]: One α := {
  one := Ring.mul_struct.unit
}

instance [Ring α]: Neg α := {
  neg := Ring.neg
}

instance [Ring α]: Sub α := {
  sub := Ring.sub
}


instance [Ring α]: Monoid α := Ring.mul_struct

instance [Ring α]: CommGroup α := Ring.add_struct


example [Ring α] (a: α): Ring.mul a 1 = a := by
  exact op_unit_right a

theorem Ring.add_assoc [Ring α] (a b c: α): a + b + c = a + (b + c) := by
  exact Ring.add_struct.assoc a b c

theorem Ring.add_zero_left [Ring α] (a: α): 0 + a = a := by
  exact Ring.add_struct.identity.left a

theorem Ring.add_zero_right [Ring α] (a: α): a + 0 = a := by
  exact Ring.add_struct.identity.right a

theorem Ring.add_neg_left [Ring α] (a: α): -a + a = 0 := by
  exact Ring.add_struct.inverse.left a

theorem Ring.add_neg_right [Ring α] (a: α): a + -a = 0 := by
  exact Ring.add_struct.inverse.right a

theorem Ring.mul_assoc [Ring α] (a b c: α): a * b * c = a * (b * c) := by
  exact Ring.mul_struct.assoc a b c

theorem Ring.mul_one_left [Ring α] (a: α): 1 * a = a := by
  exact Ring.mul_struct.identity.left a

theorem Ring.mul_one_right [Ring α] (a: α): a * 1 = a := by
  exact Ring.mul_struct.identity.right a

theorem Ring.distrib_left [Ring α] (a b c: α): a * (b + c) = (a * b) + (a * c) := by
  exact Ring.distrib.left a b c

theorem Ring.distrib_right [Ring α] (a b c: α): (a + b) * c = (a * c) + (b * c) := by
  exact Ring.distrib.right a b c

theorem Ring.mul_zero_left [Ring α] (a: α): 0 * a = 0 := by
  apply add_cancel_left (a := 0 * a)
  calc
    (0 * a) + (0 * a)
    _ = (0 + 0) * a := by rw [distrib_right]
    _ = 0 * a := by rw [add_zero_left]
    _ = 0 * a + 0 := by rw [add_zero_right]


theorem Ring.sub_self [Ring α] (a: α): a - a = 0 := by
  apply negop_self

theorem Ring.neg_sub [Ring α] (a b: α): a - b = -(b - a) := by
  sorry

theorem Ring.mul_neg [Ring α] (a b: α): a * (-b) = -(a * b) := by
  sorry

theorem Ring.neg_zero [Ring α]: -(0: α) = 0 := by
  apply inv_unit

theorem Ring.sub_zero_iff [Ring α] {a b: α}: a - b = 0 ↔ a = b := by
  sorry

theorem Ring.distrib_sub_left [Ring α] (a b c: α): a * (b - c) = a * b - a * c := by
  sorry

class CommRing (α: Type u) extends Ring α where
  mul_comm: ∀ x y: α, x * y = y * x


theorem mul_zero_right [Ring R] (a: R): a * 0 = 0 := by
  sorry

-- (-1) * a = -a.
theorem mul_neg_one [Ring R] (a: R): (-1) * a = -a := by
  sorry

-- If 0 = 1 the ring is trivial.
theorem Ring.zero_eq_one_trivial [Ring R] (h: 0 = 1): ∀ a b: R, a = b := by
  sorry
