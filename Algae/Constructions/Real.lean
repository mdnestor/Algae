import Algae.Constructions.Rational
import Algae.Topology.MetricSpace

/-

Construction of the reals.

Want to show:
- field
- poset/complete lattice

-/

def CauchySequenceRelation: Endorelation (ℕ → ℚ) :=
  sorry

def Real: Type :=
  Quotient ⟨CauchySequenceRelation, sorry⟩

abbrev ℝ: Type :=
  Real

instance: Field ℝ := sorry

-- also: that ℝ is a complete metric space
