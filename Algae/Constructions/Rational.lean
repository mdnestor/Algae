import Algae.Constructions.Integer
import Algae.RingTheory.Field
import Algae.RingTheory.Localization
import Algae.Topology.MetricSpace

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

instance: Lattice ℚ :=
  sorry

-- Need to show we have a metric on Q.
def NNRational: Type :=
  Subtype (λ x: ℚ ↦ 0 ≤ x)

instance: DistanceSpace NNRational :=
  sorry

instance Rational.metric: Metric ℚ NNRational :=
  sorry

-- Also need the endometric on rationals
instance NNRational.endometric: Endometric NNRational :=
  sorry

theorem NNRational.endometric_obedient: NNRational.endometric.obedient := by
  sorry

theorem NNRational.distance_complete: DistanceComplete NNRational := by
  sorry
