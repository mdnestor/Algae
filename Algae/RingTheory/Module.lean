import Algae.RingTheory.Ring
import Algae.GroupTheory.Action

/-

Define of an R-module on X where R is a ring and X is a group.

-/

variable {R: Type u} {X: Type v}

open Ring

local instance [Magma X]: Add X := ⟨op⟩
local instance [Pointed X]: Zero X := ⟨unit⟩
local instance [Group X]: Neg X := ⟨inv⟩
local instance [Group X]: Sub X := ⟨invop⟩

class Module (R: Type u) (X: Type v) [Ring R] [CommGroup X] extends Action R X where
  smul_distributive_left: ∀ (r: R) (x₁ x₂: X),
    r • (x₁ + x₂) = r • x₁ + r • x₂
  smul_distributive_right: ∀ (r₁ r₂: R) (x: X),
    (r₁ + r₂) • x = r₁ • x + r₂ • x

-- For convenience assume R is a ring and X is a group from now on.

variable {R: Type u} {X: Type v} [Ring R] [CommGroup X]

theorem smul_distributive_left [Module R X] (r: R) (x₁ x₂: X):
  r • (x₁ + x₂) = r • x₁ + r • x₂ := by
  exact Module.smul_distributive_left r x₁ x₂

theorem smul_distributive_right [Module R X] (r₁ r₂: R) (x: X):
  (r₁ + r₂) • x = r₁ • x + r₂ • x := by
  exact Module.smul_distributive_right r₁ r₂ x



-- Some elementary theorems about modules.
-- Often the symbol `0` by itself will be assumed to be the natural number zero
-- To do be explicit write either `0: R` or `0: X` to clarify you mean in R or X resp.

theorem smul_zero_left [Module R X] (x: X): (0:R) • x = 0 := by
  apply op_cancel_left (a := (0:R) • x)
  calc
    (0:R) • x + (0:R) • x
      = ((0:R) + (0:R)) • x := by rw [smul_distributive_right]
    _ = (0:R) • x           := by rw [@op_unit_left]
    _ = (0:R) • x + 0       := by rw [op_unit_right]

theorem smul_zero_right [Module R X] (r: R): r • (0:X) = 0 := by
  sorry

theorem smul_neg_one [Module R X] (x: X): (-1:R) • x = -x := by
  sorry
