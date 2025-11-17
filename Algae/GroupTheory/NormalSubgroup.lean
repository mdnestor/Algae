import Algae.GroupTheory.Group
import Algae.GroupTheory.Action

variable {α: Type u}

open Group

-- The (left) conjugation by an element g ∈ G of a group is the map a ↦ gag⁻¹.
-- This is a left action of the group on itself.
-- (The map a ↦ g⁻¹ag is the right conjugation since it corresponds to a right action.)

def Conjugate [Group α] (g: α): α → α :=
  λ a ↦ g + a + -g

def Conjugate.action [Group α]: Action α α := {
  act := Conjugate
  op := by
    intro a b x
    simp [Conjugate]
    apply Eq.symm
    calc
       ((a + b) + x) + -(a + b)
       _ = ((a + b) + x) + (-b + -a) := by rw [inv_op]
       _ = a + (b + x + -b) + -a := by simp [op_assoc]
  id := by
    intro
    rw [Conjugate]
    rw [inv_unit, op_unit_left, op_unit_right]
}

-- A normal subgroup is one which is invariant under conjugation.

class Group.normalSubgroup [G: Group α] (S: Set α) extends toSubgroup: G.sub S where
  conj_invariant: Conjugate.action.invariant_set S

-- In a commutative group, conjugation is trivial since gag⁻¹ = agg⁻¹ = a.

theorem CommGroup.conjugate_trivial [CommGroup α] (g: α): Conjugate g = Function.id := by
  funext
  rw [Conjugate, op_comm, ←op_assoc, op_inv_left, op_unit_left, Function.id]

-- Thus in a commutative group, every subgroup is normal.

theorem CommGroup.subgroup_normal [G: CommGroup α] {S: Set α} (h: G.sub S): G.normalSubgroup S := by
  constructor
  intro _ _ hx
  simp [Conjugate.action, CommGroup.conjugate_trivial]
  exact hx



-- Given an element g and set S, the (left) coset is defined g + S = {g + a | a ∈ S}.

def Coset [Magma α] (g: α) (S: Set α): Set α :=
  Set.image (λ a ↦ op g a) S

-- Given a set S, there is a relation that says a related to b if a + S = b + S.

def Coset.relation [Magma α] (S: Set α): Endorelation α :=
  λ a b ↦ Coset a S = Coset b S

-- TODO: simplify this? is just pullback of equality..
theorem Coset.equivalence [Magma α] (S: Set α): Equivalence (Coset.relation S) := by
  constructor
  · intro; apply Eq.refl
  · intro _ _ h; exact Eq.symm h
  · intro _ _ _ h1 h2; exact Eq.trans h1 h2

def Coset.quotient [Magma α] (S: Set α): Type u :=
  Quotient ⟨Coset.relation S, Coset.equivalence S⟩

def QuotientGroup [G: Group α] (H: Set α) (h: G.normalSubgroup H): Group (Coset.quotient H) := {
  unit := Quotient.mk _ unit
  op := sorry
  identity := sorry
  assoc := sorry
  inv := sorry
  inverse := sorry
}
