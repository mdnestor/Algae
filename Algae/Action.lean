import Algae.Structure

variable {α: Type u} {X: Type v}

class Action (α: Type u) (X: Type v) extends Monoid α where
  act: α → X → X
  act_assoc: ∀ (a b: α) (x: X), act a (act b x) = act (op a b) x
  act_id: ∀ (x: X), act unit x = x

instance [Action α X]: SMul α X := {
  smul := Action.act
}

-- Every monoid has a unital action on itself.
example [Monoid α]: Action α α := {
  act := op
  act_assoc := by
    intro a b c
    exact Eq.symm (Monoid.assoc a b c)
  act_id := id_left
}

-- Given an action of M on X, the orbit of x₀
-- is the set of all x reachable by some action.
def Orbit [Action α X] (x₀: X): Set X :=
  λ x ↦ ∃ a: α, a • x₀ = x

-- Given an action of M on X, the stabilizer of x
-- is the set of a in M which fix x.
def Stabilizer [Action α X] (x: X): Set α :=
  λ a ↦ a • x = x
