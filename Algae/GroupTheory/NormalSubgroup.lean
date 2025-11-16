import Algae.GroupTheory.Group
import Algae.GroupTheory.Action

variable {α: Type u}

open Group

def Conjugate [Group α] (g: α): α → α :=
  λ a ↦ (-g + a) + g

def Conjugate.action [Group α]: Action α α := {
  act := Conjugate
  op := by
    intro a b x
    simp [Conjugate]
    apply Eq.symm
    calc
       (-(a + b) + x) + (a + b)
       _ = ((-b + -a) + x) + (a + b) := by rw [inv_op]
       _ = -b + (-a + x + a) + b := by simp [op_assoc]
  id := by
    intro
    rw [Conjugate]
    rw [inv_unit, op_unit_left, op_unit_right]
}


class Group.normalSubgroup [G: Group α] (S: Set α) extends toSubgroup: G.sub S where
  conj_invariant: Conjugate.action.invariant_set S

theorem CommGroup.conjugate_trivial [CommGroup α] (g: α): Conjugate g = Function.id := by
  funext
  rw [Conjugate, op_comm, ←op_assoc, op_inv_right, op_unit_left, Function.id]

theorem CommGroup.subgroup_normal [G: CommGroup α] {S: Set α} (h: G.sub S): G.normalSubgroup S := by
  constructor
  intro _ _ hx
  simp [Conjugate.action, CommGroup.conjugate_trivial]
  exact hx

def Coset [Magma α] (g: α) (S: Set α): Set α :=
  Set.image (λ a ↦ op g a) S

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
