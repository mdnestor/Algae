import Algae.SetTheory.Relation
import Algae.Constructions.Natural
import Algae.RingTheory.Localization

/-

Construction of the integers.

Want to show they are
- commutative ring
- possibly cancellative wrt. addition
- partial order / total order / lattice

-/

-- We can construct the type of integers via the Grothendieck construction.
-- This gives us an additive commutative monoid.

def Integer: Type :=
  @Localization.quotient ℕ (Set.full ℕ) (CommSemiring.toAddMonoid) (Monoid.full_sub _)

def PositiveRational: Type :=
  @Localization.quotient ℕ (Set.full ℕ) (CommSemiring.toMulMonoid) (Monoid.full_sub _)

abbrev ℤ: Type :=
  Integer

instance Integer.AddGroup: CommGroup ℤ :=
  @Localization.GroupOfDifferences ℕ (CommSemiring.toAddMonoid)

-- TODO: multiplicative monoid on integers.
