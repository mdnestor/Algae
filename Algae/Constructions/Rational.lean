/-

Construction of the rationals.

Need to show
- field
- poset/lattice

TODO:
- integrate localization

-/

import Algae.Constructions.Integer
import Algae.RingTheory.Field

-- (a, b) ∼ (c, d) if a * d = b * c
def QuotientRelation: Endorelation (ℤ × ℤ) :=
  fun (a, b) (c, d) => a * d = b * c

def Rational: Type :=
  Quotient ⟨QuotientRelation, sorry⟩

abbrev ℚ: Type :=
  Rational

instance: Field ℚ := sorry
