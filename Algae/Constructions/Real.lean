import Algae.Constructions.Rational
import Algae.Topology.MetricSpace

/-

Construction of the reals.

Want to show:
- field
- poset/complete lattice

-/

def Real: Type :=
  CauchyRelation.quotient
    NNRational.distance_complete
    NNRational.endometric
    NNRational.endometric_obedient
    Rational.metric

abbrev ℝ: Type :=
  Real

instance: Field ℝ := sorry

instance: Lattice ℚ :=
  sorry

-- also: that ℝ is a complete metric space
