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
  @Localization.quotient.full ℕ CommSemiring.toAddMonoid

def NonnegRational: Type :=
  @Localization.quotient.full ℕ CommSemiring.toMulMonoid

abbrev ℤ: Type :=
  Integer

instance: CommGroup ℤ :=
  @Localization.Localization.full ℕ CommSemiring.toAddMonoid

instance: CommRing ℤ :=
  sorry
