import Algae.RingTheory.Field
import Algae.SetTheory.Relation

/-

Defines localization of a commutative monoid, as well as extensions to rings.

- Given a commutative monoid M and a submonoid S, define the localization M / S.
- When S = M then we get the group of differences of M.

For rings, there are additive/multiplicative variants of the localization.

1. Additive localization (group of differences):
  - Equivalence: (a₁, b₁) ≃ (a₂, b₂) := ∃ k, a₁ + b₂ + k = a₂ + b₁ + k

  - Addition: (a₁ - b₁) + (a₂ - b₂) := (a₁ + a₂) - (b₂ + b₂)

  - Multiplication: (a₁ - b₁) * (a₂ - b₂) = (a₁a₂ + b₁b₂) - (a₁b₂ + a₂b₁)

2. Multiplicative localization:
  - Equivalence: (a₁, b₁) ≃ (a₂, b₂) := ∃ k, k * (a₁ * b₂ - a₂ * b₁) = 0

                          equivalently, ∃ k, a₁ * b₂ * k = a₂ * b₁ * k

  - Multiplication: (a₁ / b₁) * (a₂ / b₂) := (a₁ * a₂) / (b₁ * b₂)

  - Addition: (a₁ / b₁) + (a₂ / b₂) = (a₁b₂ + a₂b₁) / (b₁b₂)

In the former case, multiplication is called the "upper" operation
in the latter, addition is called the "lower" operation.

TODO:
- Prove when R is a semiring and S = R then R/S is a ring.
- Prove when R is an integral domain and S = R \ {0} then R/S is a field.
- How to systematically lift order structure?
- (Subobject) Construct an embedding R -> R/S sending x to (x, unit).
- (Idempotence) Prove if G is already a group then G/G is isomorphic to G.
- Prove if S = R then the multiplicative localization is the trivial ring
  (since 0 is given an inverse, then 1 = 0 * 0⁻¹ = 0 → 0 = 1)

-/

namespace Localization

section Monoid

variable {α: Type u} [M: CommMonoid α] {β: Set α}

open Monoid

-- Define the relation on α × β.

def relation (β: Set α): α × β → α × β → Prop :=
  λ (a₁, ⟨b₁, _⟩) (a₂, ⟨b₂, _⟩) ↦ ∃ t ∈ β, a₁ + b₂ + t = a₂ + b₁ + t

instance: HasEquiv (α × β) := {
  Equiv := relation β
}

-- Prove it is an equivalence relation.

theorem equivalence (h: M.sub β): Equivalence (relation β) := {
  refl := by
    intro (a, b)
    exists 0
    constructor
    · exact h.unit_mem
    ·  rw [op_unit_right]
  symm := by
    intro (a₁, b₁) (a₂, b₂) ⟨t, ht₁, ht₂⟩
    exists t
    constructor
    · exact ht₁
    · exact Eq.symm ht₂
  trans := by
    intro (a₁, b₁) (a₂, b₂) (a₃, b₃) ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
    exists t₁ + t₂ + b₂
    constructor
    · repeat apply h.op_closed
      · exact ht₁₁
      · exact ht₂₁
      · exact b₂.property
    · calc
        a₁ + b₃ + (t₁ + t₂ + b₂)
        _ = a₁ + (((b₃ + t₁) + t₂) + b₂) := by simp [op_assoc]
        _ = a₁ + (b₂ + ((t₁ + b₃) + t₂)) := by simp [op_comm]
        _ = (a₁ + b₂ + t₁) + b₃ + t₂     := by simp [op_assoc]
        _ = (a₂ + b₁ + t₁) + b₃ + t₂     := by rw [ht₁₂]
        _ = (a₂ + (b₁ + t₁)) + b₃ + t₂   := by simp [op_assoc]
        _ = ((b₁ + t₁) + a₂) + b₃ + t₂   := by simp [op_comm]
        _ = b₁ + t₁ + (a₂ + b₃ + t₂)     := by simp [op_assoc]
        _ = b₁ + t₁ + (a₃ + b₂ + t₂)     := by rw [ht₂₂]
        _ = ((b₁ + t₁) + a₃) + b₂ + t₂   := by simp [op_assoc]
        _ = (a₃ + (b₁ + t₁)) + b₂ + t₂   := by simp [op_comm]
        _ = a₃ + b₁ + (t₁ + (b₂ + t₂))   := by simp [op_assoc]
        _ = a₃ + b₁ + (t₁ + (t₂ + b₂))   := by simp [op_comm]
        _ = a₃ + b₁ + (t₁ + t₂ + b₂)     := by simp [op_assoc]
}

-- Define the quotient.

def setoid (h: M.sub β): Setoid (α × β) := {
  r := relation β
  iseqv := equivalence h
}



def quotient (h: M.sub β): Type u :=
  Quotient (setoid h)

def quotient.unit (h: M.sub β): quotient h :=
  Quotient.mk _ (0, ⟨0, h.unit_mem⟩)


-- Lift the operation "add" to the quotient.
-- first define the "pre" operation on α × β then prove it lifts.
def quotient.op_pre (h: M.sub β): Op (α × β) :=
  λ (a₁, ⟨b₁, h₁⟩) (a₂, ⟨b₂, h₂⟩) ↦ (a₁ + a₂, ⟨b₁ + b₂, h.op_closed b₁ b₂ h₁ h₂⟩)

theorem quotient.op_lifts (h: M.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → Quotient.mk (setoid h) (quotient.op_pre h a b) = Quotient.mk (setoid h) (quotient.op_pre h c d) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
  apply Quotient.sound
  exists t₁ + t₂
  constructor
  · apply h.op_closed
    · exact ht₁₁
    · exact ht₂₁
  · calc
      a₁ + b₁ + (c₂ + d₂) + (t₁ + t₂)
      _ = (a₁ + (b₁ + c₂) + d₂ + t₁) + t₂   := by simp [op_assoc]
      _ = (a₁ + (c₂ + b₁) + d₂ + t₁) + t₂   := by simp [op_comm]
      _ = a₁ + c₂ + ((b₁ + d₂) + t₁) + t₂   := by simp [op_assoc]
      _ = a₁ + c₂ + (t₁ + (b₁ + d₂)) + t₂   := by simp [op_comm]
      _ = (a₁ + c₂ + t₁) + (b₁ + d₂ + t₂)   := by simp [op_assoc]
      _ = (c₁ + a₂ + t₁) + (d₁ + b₂ + t₂)   := by rw [ht₁₂, ht₂₂]
      _ = c₁ + ((a₂ + t₁) + d₁) + (b₂ + t₂) := by simp [op_assoc]
      _ = c₁ + (d₁ + (a₂ + t₁)) + (t₂ + b₂) := by simp [op_comm]
      _ = c₁ + d₁ + (a₂ + ((t₁ + t₂) + b₂)) := by simp [op_assoc]
      _ = c₁ + d₁ + (a₂ + (b₂ + (t₁ + t₂))) := by simp [op_comm]
      _ = c₁ + d₁ + (a₂ + b₂) + (t₁ + t₂)   := by simp [op_assoc]

def quotient.op (h: M.sub β): Op (quotient h) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.op_lifts h)


-- Show α / β is a commutative monoid.

instance Localization (h: M.sub β): CommMonoid (quotient h) := {
  unit := quotient.unit h
  op := quotient.op h
  identity := by
    constructor <;> (
      intro x
      refine Quotient.inductionOn x ?_
      intro (a, ⟨b, hb⟩)
      apply Quotient.sound
      exists 0
      constructor
      exact h.unit_mem
    )
    simp [op_unit_left]
    simp [op_unit_right]
  assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intros
    apply Quotient.sound
    exists 0
    constructor
    · exact h.unit_mem
    · simp [op_assoc]
  comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intros
    apply Quotient.sound
    exists 0
    constructor
    · exact h.unit_mem
    · simp [op_comm]
}

def setoid.full: Setoid (α × @Set.full α) :=
  setoid M.full_sub

abbrev quotient.full (α: Type u) [M: CommMonoid α]: Type u :=
  quotient M.full_sub

def quotient.inv_pre: α × @Set.full α → α × @Set.full α :=
  λ (a, b) =>(b, ⟨a, by trivial⟩)

theorem quotient.inv.lifts: ∀ a b: α × @Set.full α, a ≈ b → Quotient.mk setoid.full (quotient.inv_pre a) = Quotient.mk setoid.full (quotient.inv_pre b) := by
  intro (a₁, ⟨b₁, h₁⟩) (a₂, ⟨b₂, h₂⟩) ⟨t, ht₁, ht₂⟩
  apply Quotient.sound
  exists t
  constructor
  · trivial
  · calc
      b₁ + a₂ + t
      _ = a₂ + b₁ + t := by simp [op_comm]
      _ = a₁ + b₂ + t := by rw [ht₂]
      _ = b₂ + a₁ + t := by simp [op_comm]

def quotient.inv: quotient.full (α := α) → quotient.full (α := α) :=
  λ x ↦ Quotient.liftOn x _ quotient.inv.lifts

-- The "full" localization on the whole monoid (i.e. the group of differences.)
def Localization.group_of_differences: CommGroup (quotient.full α) := {
  inv := quotient.inv
  inverse := by
    constructor <;> (
      intro x
      refine Quotient.inductionOn x ?_
      intro (a, ⟨b, hb⟩)
      apply Quotient.sound
      exists 0
      constructor
      · trivial
      · simp [op_unit_right, op_comm]
    )
}

end Monoid

section Additive

-- The additive localizatoin.

variable {α: Type u} [R: Semiring α] {β: Set α}

-- The "upper" operation, i.e. the multiplication when we are localizing addition.
-- This seems to require β to be an ideal...
-- worst case we can take β = full?
def quotient.upper.op_pre (h: R.toAddMonoid.sub β): Op (α × β) :=
  λ (a₁, ⟨b₁, h₁⟩) (a₂, ⟨b₂, h₂⟩) ↦ (a₁ * a₂ + b₁ * b₂, ⟨a₁ * b₂ + a₂ * b₁, by {
    sorry
  }⟩)

theorem quotient.upper.op_lifts (h: R.toAddMonoid.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → Quotient.mk (setoid h) (quotient.upper.op_pre h a b) = Quotient.mk (setoid h) (quotient.upper.op_pre h c d) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
  apply Quotient.sound
  sorry

def quotient.upper.op (h: R.toAddMonoid.sub β): Op (quotient h) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.upper.op_lifts h)

-- The additive localization of a semiring.
instance Localization.additive [R: Semiring α] (h: R.toAddMonoid.sub β): Semiring (quotient h) := {
  add       := (Localization h).op
  zero      := (Localization h).unit
  add_assoc := (Localization h).assoc
  add_zero  := (Localization h).identity
  add_comm  := (Localization h).comm
  mul := quotient.upper.op h
  one := sorry
  mul_assoc := sorry
  mul_one := sorry
  distrib := sorry
}

-- If we localize by all elements, we get a ring.
instance Localization.additive_group_of_differences [R: Semiring α]: Ring (quotient R.toAddMonoid.full_sub) := {
  neg := sorry
  add_neg := sorry
}

-- TODO: also the additive localization of a commutative semiring should give a commutative ring.

end Additive

section Multiplicative

-- Multiplicative localization.

variable {α: Type u} [R: CommRing α] {β: Set α}

-- The "lower" operation, i.e. addition.
-- (a, b) * (c, d)
-- a/b * c/d  =  (ac)/(bd)
-- a/b + c/d = (ad + bc) / (bd)
def quotient.lower.op_pre (h: R.toMulMonoid.sub β): Op (α × β) :=
  λ (a₁, ⟨b₁, h₁⟩) (a₂, ⟨b₂, h₂⟩) ↦ (a₁ * b₂ + a₂ * b₁, ⟨b₁ * b₂, h.op_closed b₁ b₂ h₁ h₂⟩)

theorem quotient.lower.op_lifts (h: R.toMulMonoid.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → Quotient.mk (setoid h) (quotient.lower.op_pre h a b) = Quotient.mk (setoid h) (quotient.lower.op_pre h c d) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
  apply Quotient.sound
  exists t₁ * t₂
  constructor
  · apply h.op_closed
    · exact ht₁₁
    · exact ht₂₁
  · sorry

def quotient.lower.op (h: R.toMulMonoid.sub β): Op (quotient h) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.lower.op_lifts h)

def quotient.lower.inv_pre: α × β → α × β :=
  λ (r, s) ↦ (-r, s)

theorem quotient.lower.inv_lifts (h: R.toMulMonoid.sub β): ∀ a b: (α × β), a ≈ b → Quotient.mk (setoid h) (quotient.lower.inv_pre a) = Quotient.mk (setoid h) (quotient.lower.inv_pre b) := by
  intro _ _ ⟨t, ht₁, ht₂⟩
  apply Quotient.sound
  exists t
  constructor
  · exact ht₁
  · sorry

def quotient.lower.inv (h: R.toMulMonoid.sub β): quotient h → quotient h :=
  λ x ↦ Quotient.liftOn x _ (quotient.lower.inv_lifts h)

-- The multiplicative localization of a commutative ring.
instance Localization.multiplicative [R: CommRing α] (h: R.toMulMonoid.sub β): CommRing (quotient h) := {
  mul       := (Localization h).op
  one       := (Localization h).unit
  mul_assoc := (Localization h).assoc
  mul_one   := (Localization h).identity
  mul_comm  := (Localization h).comm
  add := quotient.lower.op h
  zero := Quotient.mk _ (0, ⟨1, h.unit_mem⟩)
  add_assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
    apply Quotient.sound
    exists 1
    constructor
    · exact h.unit_mem
    · calc
        ((a₁ * b₂ + b₁ * a₂) * c₂ + c₁ * (a₂ * b₂)) * (a₂ * (b₂ * c₂)) * 1
        _ = ((a₁ * b₂ * c₂ + b₁ * a₂ * c₂) + c₁ * (a₂ * b₂)) * (a₂ * (b₂ * c₂)) * 1   := by simp [distrib_right]
        _ = (a₁ * (b₂ * c₂) + b₁ * (a₂ * c₂) + c₁ * (a₂ * b₂)) * (a₂ * (b₂ * c₂)) * 1 := by simp [mul_assoc]
        _ = (a₁ * (b₂ * c₂) + b₁ * (c₂ * a₂) + c₁ * (b₂ * a₂)) * (a₂ * (b₂ * c₂)) * 1 := by simp [mul_comm]
        _ = (a₁ * (b₂ * c₂) + (b₁ * c₂ * a₂ + c₁ * b₂ * a₂)) * (a₂ * (b₂ * c₂)) * 1   := by simp [mul_assoc, add_assoc]
        _ = (a₁ * (b₂ * c₂) + (b₁ * c₂ + c₁ * b₂) * a₂) * (a₂ * (b₂ * c₂)) * 1        := by simp [distrib_right]
        _ = (a₁ * (b₂ * c₂) + (b₁ * c₂ + c₁ * b₂) * a₂) * (a₂ * b₂ * c₂) * 1          := by simp [mul_assoc]
  add_zero := by
    constructor <;> (
      intro x
      refine Quotient.inductionOn x ?_
      intro ⟨a₁, a₂⟩
      apply Quotient.sound
      exists 1
      constructor
      · exact h.unit_mem
    )
    · calc
      (0 * a₂ + a₁ * 1) * a₂ * 1
      _ = a₁ * (1 * a₂) * 1 := by simp [mul_zero_left, add_zero_left, mul_assoc]
    · calc
      (a₁ * 1 + 0 * a₂) * a₂ * 1
      _ = a₁ * (a₂ * 1) * 1 := by simp [mul_zero_left, add_zero_right, mul_one_right]
  neg := quotient.lower.inv h
  add_neg := by
    constructor
    · intro x
      refine Quotient.inductionOn x ?_
      intro ⟨a₁, a₂⟩
      apply Quotient.sound
      sorry
    · sorry
  add_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    apply Quotient.sound
    sorry
  distrib := by
    constructor
    · intro x y z
      refine Quotient.inductionOn₃ x y z ?_
      intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
      apply Quotient.sound
      sorry
    · sorry
}

-- TODO: if we localize by all nonzero elements, we should get a field.

/-
synthesized type class instance is not definitionally equal to expression inferred by typing rules, synthesized
  @instCommMonoidOfCommSemiring α (@CommRing.toCommSemiring α R✝)
inferred
  @CommSemiring.toMulMonoid α (@CommRing.toCommSemiring α R.R)
-/

-- instance Localization.field_of_fractions [R: IntegralDomain α]: Field (quotient R.nonzero_submonoid) :=
--   sorry

end Multiplicative



-- Lifting the order structure to the localization
-- (a, b) ≤ (c, d)

section OrderLift

open Monoid

variable {α: Type u} [P: PartialOrder α] [M: CommMonoid α] {β: Set α}

def order_compatible (M: CommMonoid α) (P: PartialOrder α): Prop :=
  ∀ {a b c: α}, a ≤ b → a + c ≤ b + c

def quotient.le_pre: Endorelation (α × β) :=
  λ (a₁, a₂) (b₁, b₂) ↦ ∃ t, a₁ + b₂ + t ≤ b₁ + a₂ + t

instance: Trans P.le P.le P.le := {
  trans := @P.transitive
}

-- Need the monoid M to have the property
-- a ≤ b ↔ a + c ≤ b + c
theorem quotient.le_lifts_imp (h: order_compatible M P): ∀ a b c d: (α × β), a ≈ c → b ≈ d → quotient.le_pre a b → quotient.le_pre c d := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩ ⟨t, ht⟩
  let t' := a₂ + b₁ + t₁ + t₂ + t
  exists t'
  calc
    c₁ + d₂ + (a₂ + b₁ + t₁ + t₂ + t)
      = (c₁ + a₂ + t₁) + (b₁ + d₂ + t₂) + t := by sorry
    _ = (a₁ + c₂ + t₁) + (d₁ + b₂ + t₂) + t := by rw [ht₁₂, ht₂₂]
    _ = (a₁ + b₂ + t) + (c₂ + d₁ + t₁ + t₂) := by sorry
    _ ≤ (b₁ + a₂ + t) + (c₂ + d₁ + t₁ + t₂) := by apply h ht
    _ ≤ d₁ + c₂ + (a₂ + b₁ + t₁ + t₂ + t) := by sorry

theorem quotient.le_lifts (h: order_compatible M P) (hB: M.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → quotient.le_pre a b = quotient.le_pre c d := by
  intro a b c d h₁ h₂
  simp
  constructor
  exact le_lifts_imp h a b c d h₁ h₂
  exact le_lifts_imp h c d a b ((equivalence hB).symm h₁) ((equivalence hB).symm h₂)

def quotient.le (h₀: order_compatible M P) (h: M.sub β): Endorelation (quotient h) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.le_lifts h₀ h)

-- a-b ≤ c-d ↔ a+d ≤ b+c

-- Show if a~a' and b~b' and a≤b then a'≤b'

section MultiplicativeOrderLift

section OrderLift

open Monoid


def quotient.mul_le_pre: Endorelation (α × β) :=
  λ (a₁, a₂) (b₁, b₂) ↦ ∃ t, a₁ + a₂ + 2 • b₂ + t ≤ b₁ + 2 • a₂ + b₂ + t

theorem quotient.mul_le_lifts_imp (h: order_compatible M P): ∀ a b c d: (α × β), a ≈ c → b ≈ d → quotient.mul_le_pre a b → quotient.mul_le_pre c d := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩ ⟨t, ht⟩
  let t': α := 2•a₂ + b₁ + b₂ + t₁ + t₂ + t
  exists t'
  calc
    c₁ + c₂ + 2 • d₂ + (2•a₂ + b₁ + b₂ + t₁ + t₂ + t)
    _ = (c₁ + a₂ + t₁) + (b₁ + d₂ + t₂) + (a₂ + b₂ + c₂ + d₂ + t) := by sorry
    _ = (a₁ + c₂ + t₁) + (d₁ + b₂ + t₂) + (a₂ + b₂ + c₂ + d₂ + t) := by rw [ht₁₂, ht₂₂]
    _ = (a₁ + a₂ + 2 • b₂ + t) + (2•c₂ + d₁ + d₂ + t₁ + t₂) := by sorry
    _ ≤ (b₁ + 2 • a₂ + b₂ + t) + (2•c₂ + d₁ + d₂ + t₁ + t₂) := by apply h ht
    _ ≤ d₁ + 2 • c₂ + d₂ + (2•a₂ + b₁ + b₂ + t₁ + t₂ + t) := sorry

theorem quotient.mul_le_lifts (h: order_compatible M P) (hB: M.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → quotient.mul_le_pre a b = quotient.mul_le_pre c d := by
  intro a b c d h₁ h₂
  simp
  constructor
  exact mul_le_lifts_imp h a b c d h₁ h₂
  exact mul_le_lifts_imp h c d a b ((equivalence hB).symm h₁) ((equivalence hB).symm h₂)

def quotient.mul_le (h₀: order_compatible M P) (h: M.sub β): Endorelation (quotient h) :=
  λ x y ↦ Quotient.liftOn₂ x y _ (quotient.le_lifts h₀ h)


-- a/b ≤ c/d ↔ ad^2 ≤ bd^2
