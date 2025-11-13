import Algae.SetTheory.Relation
import Algae.Constructions.Natural
import Algae.GroupTheory.DifferenceGroup

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
  @DifferenceGroup.quotient ℕ Semiring.toAddMonoid

abbrev ℤ: Type :=
  Integer

instance Integer.AddGroup: CommGroup ℤ :=
  DifferenceGroup.DifferenceGroup

instance: Zero ℤ := DifferenceGroup.DifferenceGroup.instZero
instance: Add ℤ := DifferenceGroup.DifferenceGroup.instAdd
instance: Neg ℤ := DifferenceGroup.DifferenceGroup.instNeg

namespace Integer

theorem add_assoc (a b c: ℤ): a + b + c = a + (b + c) := by
  exact op_assoc a b c




-- For the multiplicative (semiring) structure,
-- it seems for now we need to do it manually...

def Integer.one: ℤ :=
  Quotient.mk _ (1, 0)

def Integer.mul (a b: ℤ): ℤ :=
  sorry

instance Integer.MulMonoid: CommMonoid ℤ := {
  unit := Integer.one
  op := Integer.mul
  identity := sorry
  assoc := sorry
  comm := sorry
}

instance: CommRing ℤ := {
  add := Integer.AddGroup.op
  zero := Integer.AddGroup.unit
  add_assoc := Integer.AddGroup.assoc
  add_zero := Integer.AddGroup.identity
  add_comm := Integer.AddGroup.comm
  neg := Integer.AddGroup.inv
  add_neg := Integer.AddGroup.inverse
  mul := Integer.MulMonoid.op
  one := Integer.MulMonoid.unit
  mul_assoc := Integer.MulMonoid.assoc
  mul_one := Integer.MulMonoid.identity
  mul_comm := Integer.MulMonoid.comm
  distrib := sorry
}

-- (a, b) ∼ (c, d) if a + d = b + c
def DifferenceRelation: Endorelation (ℕ × ℕ) :=
  fun (a, b) (c, d) => a + d = b + c

def Integer: Type :=
  Quotient ⟨DifferenceRelation, sorry⟩



instance: Zero ℤ := sorry
instance: Add ℤ := sorry
instance: One ℤ := sorry
instance: Mul ℤ := sorry
instance: Neg ℤ := sorry
instance: LE ℤ := sorry

instance: CommRing ℤ := sorry

-- TODO: show ℤ is a poset/lattice
