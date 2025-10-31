import Algae.SetTheory

variable {α: Type u}

class Pointed (α: Type u) where
  unit: α

export Pointed (unit)

instance [Pointed α]: Zero α := {
  zero := unit
}

instance [Pointed α]: One α := {
  one := unit
}

theorem zero_eq [Pointed α]: (0: α) = unit := by
  rfl

theorem one_eq [Pointed α]: (1: α) = unit := by
  rfl
