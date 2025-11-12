/-

Construction of the integers.

Want to show they are
- commutative ring
- possibly cancellative wrt. addition
- partial order / total order / lattice

TODO:
- integrate the Grothendieck construction

-/

import Algae.SetTheory.Relation
import Algae.Constructions.Natural
import Algae.GroupTheory.GrothendieckGroup

-- def Integer: Type :=
--   @GrothendieckGroup.quotient ℕ Semiring.toAddMonoid

-- instance: CommGroup ℤ :=
--   GrothendieckGroup.GrothendieckGroup


-- (a, b) ∼ (c, d) if a + d = b + c
def DifferenceRelation: Endorelation (ℕ × ℕ) :=
  fun (a, b) (c, d) => a + d = b + c

def Integer: Type :=
  Quotient ⟨DifferenceRelation, sorry⟩

abbrev ℤ: Type :=
  Integer

instance: CommRing ℤ := sorry

-- TODO: show ℤ is a poset/lattice
