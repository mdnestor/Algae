import Algae.Monoid

variable {α: Type u} {X: Type v}

class Action (α: Type u) (X: Type v) extends Magma α where
  act: α → X → X
  compatible: ∀ a b x, act a (act b x) = act (op a b) x

class UnitalAction (α: Type u) (X: Type v) extends UnitalMagma α, Action α X where
  unit_action: ∀ x, act unit x = x

-- Every associative magma acts on itself.
def AssociativeMagma.self_action (M: AssociativeMagma α): Action α α := {
  act := M.op
  compatible := by
    intros
    apply Eq.symm
    apply M.associative
}

-- Every unital  magma acts on itself.
def Monoid.self_unital_action (M: Monoid α): UnitalAction α α := {
  act := M.op
  compatible := M.self_action.compatible
  unit_action := M.identity.left
}

def orbit (act: α → X → X) (x0: X): Set X :=
  λ x ↦ ∃ a, act a x0 = x

def stabilizer (act: α → X → X) (x: X): Set α :=
  λ a ↦ act a x = x
