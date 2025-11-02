import Algae.Monoid

variable {α: Type u} {X: Type v}

class Action (α: Type u) [Monoid α] (X: Type v) where
  act: α → X → X
  act_assoc: ∀ a b x, act (op a b) x = act a (act b x)
  act_id: LeftIdentity act unit

instance [Monoid α] [Action α X]: SMul α X := {
  smul := Action.act
}

-- Every monoid defines an action on itself.
example [Monoid α]: Action α α := {
  act := op
  act_assoc := Monoid.assoc
  act_id := Monoid.identity.left
}


-- TODO: orbit
-- Given an action of M on X, the orbit of x₀
-- is the set of all x reachable by some action.

-- TODO: stabilizer
-- Given an action of M on X, the stabilizer of x
-- is the set of a in M which fix x.

-- TODO: stabilizer forms a submonoid / subgroup
