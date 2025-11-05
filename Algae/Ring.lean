import Algae.Group

variable {α: Type u}


class Ring (α: Type u) where
  add_struct: CommGroup α
  mul_struct: Monoid α
  distrib: Distributive mul_struct.op add_struct.op

def Ring.zero [Ring α]: α := Ring.add_struct.unit
def Ring.add [Ring α]: α → α → α := Ring.add_struct.op
def Ring.neg [Ring α]: α → α := Ring.add_struct.inv
def Ring.sub [Ring α]: α → α → α := λ a b ↦ add a (neg b)
def Ring.mul [Ring α]: α → α → α := Ring.mul_struct.op
def Ring.one [Ring α]: α := Ring.mul_struct.unit

instance [Ring α]: Zero α := ⟨Ring.add_struct.unit⟩
instance [Ring α]: Add α := ⟨Ring.add⟩
instance [Ring α]: Neg α := ⟨Ring.neg⟩
instance [Ring α]: Sub α := ⟨Ring.sub⟩
instance [Ring α]: One α := ⟨Ring.mul_struct.unit⟩
instance [Ring α]: Mul α := ⟨Ring.mul⟩
instance [Ring α]: CommGroup α := Ring.add_struct
instance [Ring α]: Monoid α := Ring.mul_struct

theorem add_assoc [Ring α] (a b c: α): a + b + c = a + (b + c) := by
  apply Ring.add_struct.assoc

theorem add_zero_left [Ring α] (a: α): 0 + a = a := by
  apply Ring.add_struct.identity.left

theorem add_zero_right [Ring α] (a: α): a + 0 = a := by
  apply Ring.add_struct.identity.right

theorem add_neg_left [Ring α] (a: α): -a + a = 0 := by
  apply op_inv_left

theorem add_neg_right [Ring α] (a: α): a + -a = 0 := by
  apply op_inv_right

theorem add_comm [Ring α] (a b: α): a + b = b + a := by
  apply op_comm

theorem mul_assoc [Ring α] (a b c: α): a * b * c = a * (b * c) := by
  apply op_assoc

theorem mul_one_left [Ring α] (a: α): 1 * a = a := by
  apply op_unit_left

theorem mul_one_right [Ring α] (a: α): a * 1 = a := by
  apply op_unit_right

theorem distrib_left [Ring α] (a b c: α): a * (b + c) = (a * b) + (a * c) := by
  apply Ring.distrib.left

theorem distrib_right [Ring α] (a b c: α): (a + b) * c = (a * c) + (b * c) := by
  apply Ring.distrib.right

theorem mul_zero_left [Ring α] (a: α): 0 * a = 0 := by
  apply op_cancel_left
  calc
    (0 * a) + (0 * a)
    _ = (0 + 0) * a := by rw [distrib_right]
    _ = 0 * a := by rw [add_zero_left]
    _ = 0 * a + 0 := by rw [add_zero_right]

theorem mul_zero_right [Ring R] (a: R): a * 0 = 0 := by
  sorry

theorem sub_self [Ring α] (a: α): a - a = 0 := by
  apply invop_self

theorem neg_sub [Ring α] (a b: α): -(a - b) = b - a := by
  rw [inv_invop]

theorem neg_sub' [Ring α] (a b: α): -(a - b) = -a + b := by
  rw [neg_sub, add_comm]; rfl

theorem neg_zero [Ring α]: -(0: α) = 0 := by
  apply inv_unit

theorem sub_zero_iff [Ring α] {a b: α}: a - b = 0 ↔ a = b := by
  sorry

theorem distrib_sub_left [Ring α] (a b c: α): a * (b - c) = a * b - a * c := by
  sorry

theorem mul_neg [Ring α] (a b: α): a * (-b) = -(a * b) := by
  apply Eq.symm; apply op_unit_inverses
  rw [←distrib_left, add_neg_right, mul_zero_right]

theorem mul_neg_one [Ring α] (a: α): (-1) * a = -a := by
  apply Eq.symm
  apply op_unit_inverses
  calc
    a + -1 * a
    _ = 1 * a + -1 * a := by rw [mul_one_left]
    _ = (1 + -1) * a := by rw [distrib_right]
    _ = 0 * a := by rw [add_neg_right]
    _ = 0 := by rw [mul_zero_left]

-- If 0 = 1 the ring is trivial.
theorem zero_eq_one_trivial [Ring R] (h: (0: R) = 1): ∀ a b: R, a = b := by
  intro a b
  calc
    a
    _ = 1 * a := by rw [mul_one_left]
    _ = 0 * a := by rw [h]
    _ = 0     := by rw [mul_zero_left]
    _ = 0 * b := by rw [mul_zero_left]
    _ = 1 * b := by rw [h]
    _ = b     := by rw [mul_one_left]

class CommRing (α: Type u) extends Ring α where
  mul_comm: ∀ x y: α, x * y = y * x

theorem mul_comm [CommRing α] (a b: α): a * b = b * a := by
  apply CommRing.mul_comm
