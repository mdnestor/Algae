import Algae.GroupTheory.Group
import Algae.GroupTheory.Action

variable {α: Type u}

local instance [Monoid α]: Add α := ⟨op⟩
local instance [Monoid α]: Zero α := ⟨unit⟩
local instance [Group α]: Neg α := ⟨inv⟩

def Conjugate [Group α] (g: α): α → α :=
  λ a ↦ op (op (inv g) a) g

def Conjugate.action [Group α]: Action α α := {
  act := Conjugate
  act_op := by
    intro a b x
    to_additive
    calc
       (-(a + b) + x) + (a + b)
       _ = ((-b + -a) + x) + (a + b) := by rw [inv_op]
       _ = (-b + (-a + x)) + (a + b) := by rw [op_assoc (-b)]
       _ = -b + (-a + x) + (a + b) := by rw [op_assoc (-b)]
       _ = -b + ((-a + x) + (a + b)) := by rw [op_assoc (-b)]
       _ = -b + ((-a + x) + (a + b)) := by sorry
       _ = -b + (-a + x + a) + b := by sorry
  act_id := by
    intro
    rw [Conjugate]
    to_additive
    rw [inv_unit, op_unit_left, op_unit_right]
}

class NormalSubgroup [Group α] (S: Set α) extends Subgroup S where
  conj_invariant: Conjugate.action.invariant_set S

theorem CommGroup.conjugate_trivial [CommGroup α] (g: α): Conjugate g = Function.id := by
  funext
  rw [Conjugate, op_comm]
  to_additive
  rw [←op_assoc, op_inv_right, op_unit_left, Function.id]

theorem CommGroup.subgroup_normal [CommGroup α] {S: Set α} (h: Subgroup S): NormalSubgroup S := by
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

def QuotientGroup [Group α] (H: Set α) (h: NormalSubgroup H): Group (Coset.quotient H) := {
  unit := Quotient.mk _ unit
  op := sorry
  identity := sorry
  assoc := sorry
  inv := sorry
  inverse := sorry
}
