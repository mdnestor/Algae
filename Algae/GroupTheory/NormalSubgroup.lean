import Algae.GroupTheory.Group
import Algae.GroupTheory.Action

variable {α: Type u}

local instance [Monoid α]: Add α := ⟨op⟩
local instance [Monoid α]: Zero α := ⟨unit⟩
local instance [Group α]: Neg α := ⟨inv⟩
--local instance [Group α]: Sub α := ⟨invop⟩

def Conjugate [Group α]: Action α α := {
  act := λ g a ↦ op (op (inv g) a) g
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
    intro a
    to_additive
    rw [inv_unit, op_unit_left, op_unit_right]
}

class NormalSubgroup [Group α] (S: Set α) extends Subgroup S where
  conj_invariant: Conjugate.invariant_set S

--def Coset (S: Set α) (g: α): Set α :=

--def QuotientGroup (G: Group α) {S: Set α} (hS: NormalSubgroup S): Group (Action.quotient)
