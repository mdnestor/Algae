import Algae.RingTheory.Ring

variable {F: Type u}

open Ring

def Nonzero (F: Type u) [Zero F]: Set F :=
  λ a => a ≠ 0

class Field (F: Type u) extends CommRing F, Inv (Nonzero F) where
  mul_inverses: ∀ a: Nonzero F, a.val * a⁻¹ = 1

def Field.inverse [Field F] {a: F} (h: a ≠ 0): F :=
  (⟨a, h⟩: Nonzero F)⁻¹.val
