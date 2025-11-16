import Algae.RingTheory.Ring
import Algae.GroupTheory.Action

variable {X: Type u} {R: Type v}

open Group Ring

/-

An R-module on X consists of
- a commutative group X,
- a ring R,
- an action of R on X,
- distributive laws.

-/

class Module (X: Type u) [CommGroup X] (R: Type v) [Ring R] extends Action R X where
  distrib_scalar: ∀ (r: R) (x₁ x₂: X),
    r • (x₁ + x₂) = r • x₁ + r • x₂r
  distrib_point: ∀ (r₁ r₂: R) (x: X),
    (r₁ + r₂) • x = r₁ • x + r₂ • x

export Module (distrib_scalar distrib_point)

-- For convenience assume we have a module from now on.

variable [CommGroup X] [Ring R] [Module X R]


-- Basic facts about modules.
-- Often the symbol `0` by itself will be assumed to be the natural number zero
-- To do be explicit write either `0: R` or `0: X` to clarify you mean in R or X resp.

theorem smul_zero_left (x: X): (0:R) • x = (0:X) := by
  apply op_cancel_left (a := (0:R) • x)
  calc
    (0:R) • x + (0:R) • x
      = ((0:R) + (0:R)) • x := by rw [distrib_point]
    _ = (0:R) • x           := by rw [op_unit_left]
    _ = (0:R) • x + 0       := by rw [op_unit_right]

theorem smul_zero_right (r: R): r • (0:X) = (0:X) := by
  sorry

theorem smul_neg_one (x: X): (-1:R) • x = -x := by
  sorry
