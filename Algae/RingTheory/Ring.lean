import Algae.GroupTheory.Group

variable {α: Type u}



/-

A ring is a set with
- a commutative group structure denoted `+`
- a monoid structure denoted `*`
- `*` is distributive over `+`

A commutative ring has commutative multiplication.

-/

class Ring (α: Type u) where
  add_struct: CommGroup α
  mul_struct: Monoid α
  distrib: Distributive mul_struct.op add_struct.op

class CommRing (α: Type u) extends Ring α where
  mul_comm: Commutative mul_struct.op



namespace Ring

-- A ring structure is assumed throughout.
variable [Ring α]

-- Specializing names and giving additive/multiplicative notation.
def Ring.zero: α           := Ring.add_struct.unit
def Ring.add:  α → α → α   := Ring.add_struct.op
def Ring.neg:  α → α       := Ring.add_struct.inv
def Ring.sub:  α → α → α   := Ring.add_struct.opinv
def Ring.nmul: Nat → α → α := Ring.add_struct.nmul
def Ring.zmul: Int → α → α := Ring.add_struct.zmul
def Ring.mul:  α → α → α   := Ring.mul_struct.op
def Ring.one:  α           := Ring.mul_struct.unit
def Ring.pow:  α → Nat → α := flip Ring.mul_struct.nmul

-- Notation for 0, +, -, 1, *, ^, •
instance: Zero α       := ⟨Ring.zero⟩
instance: Add α        := ⟨Ring.add⟩
instance: Neg α        := ⟨Ring.neg⟩
instance: Sub α        := ⟨Ring.sub⟩
instance: One α        := ⟨Ring.one⟩
instance: Mul α        := ⟨Ring.mul⟩
instance: HPow α Nat α := ⟨Ring.pow⟩
instance: SMul Nat α   := ⟨Ring.nmul⟩
instance: SMul Int α   := ⟨Ring.zmul⟩

-- No idea
instance: CommGroup α := Ring.add_struct
instance: Monoid α    := Ring.mul_struct


-- Unpacking axioms with notation.
theorem add_assoc (a b c: α): a + b + c = a + (b + c) := by
  apply Ring.add_struct.assoc

theorem add_zero_left (a: α): 0 + a = a := by
  apply Ring.add_struct.identity.left

theorem add_zero_right (a: α): a + 0 = a := by
  apply Ring.add_struct.identity.right

theorem add_neg_left (a: α): -a + a = 0 := by
  apply op_inv_left

theorem add_neg_right (a: α): a + -a = 0 := by
  apply op_inv_right

theorem add_comm (a b: α): a + b = b + a := by
  apply op_comm

theorem mul_assoc (a b c: α): a * b * c = a * (b * c) := by
  apply op_assoc

theorem mul_one_left (a: α): 1 * a = a := by
  apply op_unit_left

theorem mul_one_right (a: α): a * 1 = a := by
  apply op_unit_right

theorem distrib_left (a b c: α): a * (b + c) = (a * b) + (a * c) := by
  apply Ring.distrib.left

theorem distrib_right (a b c: α): (a + b) * c = (a * c) + (b * c) := by
  apply Ring.distrib.right

theorem sub_self (a: α): a - a = 0 := by
  exact opinv_self a

theorem neg_sub (a b: α): -(a - b) = b - a := by
  rw [inv_invop]

theorem neg_sub' (a b: α): -(a - b) = -a + b := by
  rw [neg_sub, add_comm]; rfl

theorem neg_zero: -(0: α) = 0 := by
  apply inv_unit

-- nmul and npow
theorem nmul_zero (a: α): 0 • a = 0 := by
  rfl

theorem nmul_succ (a: α) (n: Nat): (n + 1) • a = (n • a) + a := by
  rfl

theorem zmul_zero (a: α): (0: Int) • a = 0 := by
  rfl

theorem npow_zero (a: α): a^0 = 1 := by
  rfl

theorem npow_one (a: α): a^1 = a := by
  apply nmul_one

-- Basic theorems
theorem sub_zero_iff {a b: α}: a - b = 0 ↔ a = b := by
  constructor
  · intro h
    apply op_cancel_right
    calc
      a - b
      _ = 0 := by rw [h]
      _ = b + -b := by rw [op_inv_right]
  · intro h
    rw [h, sub_self]

theorem mul_zero_left (a: α): 0 * a = 0 := by
  apply op_cancel_left
  calc
    0 * a + 0 * a
    _ = (0 + 0) * a := by rw [distrib_right]
    _ = 0 * a       := by rw [add_zero_left]
    _ = 0 * a + 0   := by rw [add_zero_right]

theorem mul_zero_right (a: α): a * 0 = 0 := by
  apply op_cancel_right
  calc
    a * 0 + a * 0
    _ = a * (0 + 0) := by rw [distrib_left]
    _ = a * 0       := by rw [add_zero_left]
    _ = 0 + a * 0   := by rw [add_zero_left]

theorem mul_neg_one (a: α): (-1) * a = -a := by
  apply Eq.symm
  apply op_unit_inverses
  calc
    a + -1 * a
    _ = 1 * a + -1 * a := by rw [mul_one_left]
    _ = (1 + -1) * a := by rw [distrib_right]
    _ = 0 * a := by rw [add_neg_right]
    _ = 0 := by rw [mul_zero_left]

theorem mul_neg_left (a b: α): (-a) * b = -(a * b) := by
  apply Eq.symm
  apply op_unit_inverses
  rw [←distrib_right, add_neg_right, mul_zero_left]

theorem mul_neg_right (a b: α): a * (-b) = -(a * b) := by
  apply Eq.symm
  apply op_unit_inverses
  rw [←distrib_left, add_neg_right, mul_zero_right]

theorem distrib_sub_left (a b c: α): a * (b - c) = a * b - a * c := by
  calc
    a * (b + -c)
    _ = a * b + a * -c := by rw [distrib_left]
    _ = a * b + -(a * c)  := by rw [mul_neg_right]

theorem distrib_sub_right (a b c: α): (a - b) * c = a * c - b * c := by
  calc
    (a + -b) * c
    _ = a * c + -b * c   := by rw [distrib_right]
    _ = a * c + -(b * c) := by rw [mul_neg_left]

-- If 0 = 1 the ring is trivial (singleton).
theorem zero_eq_one_trivial (h: (0: α) = 1): ∀ a b: α, a = b := by
  intro a b
  calc
    a
    _ = 1 * a := by rw [mul_one_left]
    _ = 0 * a := by rw [h]
    _ = 0     := by rw [mul_zero_left]
    _ = 0 * b := by rw [mul_zero_left]
    _ = 1 * b := by rw [h]
    _ = b     := by rw [mul_one_left]

end Ring

open Ring

theorem mul_comm [CommRing α] (a b: α): a * b = b * a := by
  apply CommRing.mul_comm
