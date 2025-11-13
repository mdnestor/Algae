import Algae.GroupTheory.Group

variable {α: Type u}

/-

A ring is a set with
- a commutative group structure denoted `+`
- a monoid structure denoted `*`
- `*` is distributive over `+`

A commutative ring has commutative multiplication.

-/

class Semiring (α: Type u) where
  add: α → α → α
  zero: α
  add_assoc: Associative add
  add_zero: Identity add zero
  add_comm: Commutative add
  mul: α → α → α
  one: α
  mul_assoc: Associative mul
  mul_one: Identity mul one
  distrib: Distributive mul add

class Ring (α: Type u) extends Semiring α where
  neg: α → α
  add_neg: Inverse add neg zero

class CommSemiring (α: Type u) extends Semiring α where
  mul_comm: Commutative mul

class CommRing (α: Type u) extends Ring α, CommSemiring α

-- Notation for 0, +, -, 1, *, ^, •

instance Semiring.toAddMonoid [Semiring α]: CommMonoid α := {
  op := add
  unit := zero
  identity := add_zero
  assoc := add_assoc
  comm := add_comm
}

instance Semiring.toMulMonoid [Semiring α]: Monoid α := {
  op := mul
  unit := one
  identity := mul_one
  assoc := mul_assoc
}

instance [CommSemiring α]: CommMonoid α := {
  op := Semiring.mul
  unit := Semiring.one
  identity := Semiring.mul_one
  assoc := Semiring.mul_assoc
  comm := CommSemiring.mul_comm
}

instance [Ring α]: CommGroup α := {
  op := Ring.toSemiring.add
  unit := Ring.toSemiring.zero
  identity := Ring.toSemiring.add_zero
  assoc := Ring.toSemiring.add_assoc
  inv := Ring.neg
  inverse := Ring.add_neg
  comm := Ring.toSemiring.add_comm
}

def Ring.sub [Ring α]: Op α :=
  Group.opinv

instance [Semiring α]: Zero α  := ⟨Semiring.zero⟩
instance [Semiring α]: Add α   := ⟨Semiring.add⟩
instance [Ring α]: Neg α        := ⟨Ring.neg⟩
instance [Ring α]: Sub α        := ⟨Ring.sub⟩
instance [Semiring α]: One α        := ⟨Semiring.one⟩
instance [Semiring α]: Mul α        := ⟨Semiring.mul⟩
instance [Semiring α]: HPow α Nat α := ⟨flip Semiring.toMulMonoid.ngen⟩
instance [Semiring α]: SMul Nat α   := ⟨Semiring.toAddMonoid.ngen⟩
instance [Ring α]: SMul Int α   := ⟨Group.zgen⟩


-- Unpacking axioms with notation.
theorem add_assoc [Semiring α] (a b c: α): a + b + c = a + (b + c) := by
  apply @op_assoc _ Semiring.toAddMonoid.toMonoid

theorem add_zero_left [Semiring α] (a: α): 0 + a = a := by
  apply @op_unit_left _ Semiring.toAddMonoid.toMonoid

theorem add_zero_right [Semiring α] (a: α): a + 0 = a := by
  apply @op_unit_right _ Semiring.toAddMonoid.toMonoid

theorem add_neg_left [Ring α] (a: α): -a + a = 0 := by
  apply op_inv_left

theorem add_neg_right [Ring α] (a: α): a + -a = 0 := by
  apply op_inv_right

theorem add_comm [Semiring α] (a b: α): a + b = b + a := by
  apply op_comm

theorem mul_assoc [Semiring α] (a b c: α): a * b * c = a * (b * c) := by
  apply op_assoc

theorem mul_one_left [Semiring α] (a: α): 1 * a = a := by
  apply op_unit_left

theorem mul_one_right [Semiring α] (a: α): a * 1 = a := by
  apply op_unit_right

theorem distrib_left [Semiring α] (a b c: α): a * (b + c) = (a * b) + (a * c) := by
  apply Semiring.distrib.left

theorem distrib_right [Semiring α] (a b c: α): (a + b) * c = (a * c) + (b * c) := by
  apply Semiring.distrib.right

theorem sub_self [Ring α] (a: α): a - a = 0 := by
  exact opinv_self a

theorem neg_sub [Ring α] (a b: α): -(a - b) = b - a := by
  rw [inv_invop]

theorem neg_sub' [Ring α] (a b: α): -(a - b) = -a + b := by
  rw [neg_sub, add_comm]; rfl

theorem neg_zero [Ring α]: -(0: α) = 0 := by
  apply inv_unit

-- nmul and npow

theorem nmul_zero [Semiring α] (a: α): 0 • a = 0 := by
  rfl

theorem nmul_succ [Semiring α] (a: α) (n: Nat): (n + 1) • a = (n • a) + a := by
  rfl

theorem zmul_zero [Ring α] (a: α): (0: Int) • a = 0 := by
  rfl

theorem npow_zero [Semiring α] (a: α): a^0 = 1 := by
  rfl

theorem npow_one [Semiring α] (a: α): a^1 = a := by
  apply ngen_one

-- Basic theorems
theorem sub_zero_iff [Ring α] {a b: α}: a - b = 0 ↔ a = b := by
  constructor
  · intro h
    apply op_cancel_right
    calc
      a - b
      _ = 0 := by rw [h]
      _ = b + -b := by rw [op_inv_right]
  · intro h
    rw [h, sub_self]

theorem mul_zero_left [Ring α] (a: α): 0 * a = 0 := by
  apply op_cancel_left
  calc
    0 * a + 0 * a
    _ = (0 + 0) * a := by rw [distrib_right]
    _ = 0 * a       := by rw [add_zero_left]
    _ = 0 * a + 0   := by rw [add_zero_right]

theorem mul_zero_right [Ring α] (a: α): a * 0 = 0 := by
  apply op_cancel_right
  calc
    a * 0 + a * 0
    _ = a * (0 + 0) := by rw [distrib_left]
    _ = a * 0       := by rw [add_zero_left]
    _ = 0 + a * 0   := by rw [add_zero_left]

theorem mul_neg_one [Ring α] (a: α): (-1) * a = -a := by
  apply Eq.symm
  apply op_unit_inverses
  calc
    a + -1 * a
    _ = 1 * a + -1 * a := by rw [mul_one_left]
    _ = (1 + -1) * a := by rw [distrib_right]
    _ = 0 * a := by rw [add_neg_right]
    _ = 0 := by rw [mul_zero_left]

theorem mul_neg_left [Ring α] (a b: α): (-a) * b = -(a * b) := by
  apply Eq.symm
  apply op_unit_inverses
  rw [←distrib_right, add_neg_right, mul_zero_left]

theorem mul_neg_right [Ring α] (a b: α): a * (-b) = -(a * b) := by
  apply Eq.symm
  apply op_unit_inverses
  rw [←distrib_left, add_neg_right, mul_zero_right]

theorem distrib_sub_left [Ring α] (a b c: α): a * (b - c) = a * b - a * c := by
  calc
    a * (b + -c)
    _ = a * b + a * -c := by rw [distrib_left]
    _ = a * b + -(a * c)  := by rw [mul_neg_right]

theorem distrib_sub_right [Ring α] (a b c: α): (a - b) * c = a * c - b * c := by
  calc
    (a + -b) * c
    _ = a * c + -b * c   := by rw [distrib_right]
    _ = a * c + -(b * c) := by rw [mul_neg_left]

-- If 0 = 1 the ring is trivial (singleton).
theorem zero_eq_one_trivial [Ring α] (h: (0: α) = 1): ∀ a b: α, a = b := by
  intro a b
  calc
    a
    _ = 1 * a := by rw [mul_one_left]
    _ = 0 * a := by rw [h]
    _ = 0     := by rw [mul_zero_left]
    _ = 0 * b := by rw [mul_zero_left]
    _ = 1 * b := by rw [h]
    _ = b     := by rw [mul_one_left]


theorem mul_comm [CommRing α] (a b: α): a * b = b * a := by
  apply CommRing.mul_comm
