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

-- def NonnegRational: Type :=
--   @Localization.quotient.full ℕ CommSemiring.toMulMonoid

abbrev ℤ: Type :=
  Integer

instance: CommGroup ℤ :=
  @Localization.Localization.group_of_differences ℕ CommSemiring.toAddMonoid

instance: CommRing ℤ :=
  sorry

example: Localization.order_compatible Natural.NaturalSemiring.toAddMonoid Natural.NaturalLattice.toPartialOrder := by
  intro a b c h₁
  exact Natural.le_add h₁

instance: Lattice ℤ := {
  le := sorry -- quotient.le
  reflexive := sorry
  transitive := sorry
  antisymmetric := sorry
  min := sorry
  max := sorry
  max_le_left := sorry
  max_le_right := sorry
  max_lub := sorry
  min_le_left := sorry
  min_le_right := sorry
  min_glb := sorry
}
