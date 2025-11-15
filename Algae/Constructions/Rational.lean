import Algae.Constructions.Integer
import Algae.RingTheory.Field
import Algae.RingTheory.Localization

/-

Construction of the rationals.

Need to show
- poset/lattice

-/

-- ℤ is an integral domain.

instance: IntegralDomain ℤ := {
  no_zero_divisors := sorry
  nontrivial := sorry
}

-- Define ℚ as the field of fractions of ℤ, which is the localization of ℤ by ℤ \ {0}.

def Rational: Type :=
  sorry

abbrev ℚ: Type :=
  Rational

instance: Field ℚ :=
  sorry
