import Algae.Constructions.Integer
import Algae.RingTheory.Field
import Algae.RingTheory.Localization

/-

Construction of the rationals.

Need to show
- field
- poset/lattice

-/

-- ℤ is an integral domain.

theorem Integer.integral_domain: Localization.IntegralDomain ℤ := by
  constructor
  · sorry
  · sorry

-- Define ℚ via the localization.

def Rational: Type :=
  Localization.quotient (Localization.nonzero_mul_closed Integer.integral_domain)

abbrev ℚ: Type :=
  Rational

instance: Field ℚ :=
  Localization.FieldOfFractions Integer.integral_domain
