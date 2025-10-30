import Algae.Group

variable {R: Type u}

class Ring (R: Type u) extends CommutativeGroup R, MulMonoid R where
  distributive: Distributive mul add

theorem distribute_mul_add_left [Ring R] (a b c: R): a * (b + c) = a * b + a * c := by
  exact Ring.distributive.left a b c

theorem distribute_mul_add_right [Ring R] (a b c: R): (a + b) * c = a * c + b * c := by
  exact Ring.distributive.right a b c

-- Zero is absorbing wrt. multiplication: 0 * a = a * 0 = 0.
theorem mul_zero_left [Ring R] (a: R): 0 * a = 0 := by
  apply add_cancel_left (a := 0 * a)
  calc
    0 * a + 0 * a
    _ = (0 + 0) * a := by rw [distribute_mul_add_right]
    _ = 0 * a       := by rw [add_zero_left]
    _ = 0 * a + 0   := by rw [add_zero_right]

theorem mul_zero_right [Ring R] (a: R): a * 0 = 0 := by
  apply add_cancel_left (a := a * 0)
  calc
    a * 0 + a * 0
    _ = a * (0 + 0) := by rw [distribute_mul_add_left]
    _ = a * 0       := by rw [add_zero_right]
    _ = a * 0 + 0   := by rw [add_zero_right]

-- (-1) * a = -a.
theorem mul_neg_one [Ring R] (a: R): (-1) * a = -a := by
  apply add_cancel_right (c := a)
  rw [add_negative_left]
  calc
    -1 * a + a
    _ = -1 * a + 1 * a := by rw [mul_one_left]
    _ = (-1 + 1) * a   := by rw [distribute_mul_add_right]
    _ = 0 * a          := by rw [add_negative_left]
    _ = 0              := by rw [mul_zero_left]

-- If 0 = 1, the ring is trivial.
theorem Ring.zero_eq_one_trivial [Ring R] (h: (0 : R) = (1 : R)): ∀ a b: R, a = b := by
  intro a b
  rw [←mul_one_right a, ←mul_one_right b, ←h, mul_zero_right, mul_zero_right]

class CommutativeRing (R: Type u) extends Ring R, CommutativeMulMonoid R
