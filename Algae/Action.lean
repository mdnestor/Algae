import Algae.Monoid

variable {M: Type u} {X: Type v}



class Action (M: Type u) (X: Type v) extends MulMagma M, SMul M X where
  smul_associative: ∀ (a b: M) (x: X), a • (b • x) = (a * b) • x

theorem smul_associative [Action M X]: ∀ (a b: M) (x: X), a • (b • x) = (a * b) • x := by
  exact Action.smul_associative

class UnitalAction (M: Type u) (X: Type v) extends UnitalMulMagma M, Action M X where
  smul_identity: ∀ (x: X), (1: M) • x = x

theorem smul_identity [UnitalAction M X]: ∀ (x: X), (1: M) • x = x := by
  exact UnitalAction.smul_identity


-- Every associative magma has an action on itself.
def AssociativeMulMagma.self_action [AssociativeMulMagma M]: Action M M := {
  smul := Mul.mul
  smul_associative := by
    intro a b x
    exact Eq.symm (mul_associative a b x)
}

-- Every monoid has a unital action on itself.
example [MulMonoid M]: UnitalAction M M := {
  smul := Mul.mul
  smul_associative := AssociativeMulMagma.self_action.smul_associative
  smul_identity := UnitalMulMagma.identity.left
}

-- Given an action of M on X, the orbit of x₀
-- is the set of all x reachable by some action.
def Orbit [Action M X] (x₀: X): Set X :=
  λ x ↦ ∃ a: M, a • x₀ = x

-- Given an action of M on X, the stabilizer of x
-- is the set of a in M which fix x.
def Stabilizer [Action M X] (x: X): Set M :=
  λ a ↦ a • x = x
