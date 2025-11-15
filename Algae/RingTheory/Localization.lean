import Algae.RingTheory.Ring

/-

The equivalence relations for group of differences of a commutative monoid and
localization of a commutative ring are identical:

For group of differences:
  a₁ + b₂ + k = a₂ + b₁ + k

For localization:
  k * (a₁ * b₂ - a₂ * b₁) = 0
              ↔
  a₁ * b₂ * k = a₂ * b₁ * k

Also importantly the way we define the "lifted" operation is identical:

For group of differences:
  (a₁ - b₁) + (a₂ - b₂) = (a₁ + a₂) - (b₂ + b₂)

For localization:
  a₁/b₁ * a₂/b₂ = a₁a₂/b₁b₂

So to generalize we need a construction that adds inverses to *some* elements
of a commutative monoid, where the "denominators" or "negatives" are taken from
some submonoid.

-/

namespace Localization

variable {α: Type u} [M: CommMonoid α] {β: Set α}

section MonoidLocalization

open Monoid

-- Define the relation on α × β.

def relation (β: Set α) [CommMonoid α]: α × β → α × β → Prop :=
  λ (a₁, ⟨b₁, _⟩) (a₂, ⟨b₂, _⟩) ↦ ∃ t ∈ β, a₁ + b₂ + t = a₂ + b₁ + t

instance (α: Type u) (β: Set α) [CommMonoid α]: HasEquiv (α × β) := {
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

def setoid [M: CommMonoid α] (h: M.sub β): Setoid (α × β) := {
  r := relation β
  iseqv := equivalence h
}

def quotient [M: CommMonoid α] (h: M.sub β): Type u :=
  Quotient (setoid h)

-- Lift the operation "add" to the quotient.

def add_pairs [h: M.sub β]: (α × β) → (α × β) → (α × β) := by
    intro (a₁, ⟨b₁, h₁⟩) (a₂, ⟨b₂, h₂⟩)
    have h: (b₁ + b₂) ∈ β := by apply h.op_closed b₁ b₂ h₁ h₂
    exact (a₁ + a₂, ⟨b₁ + b₂, h⟩)

instance [h: M.sub β]: Add (α × β) := {
  add := add_pairs
}

theorem quotient_op (h: M.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → Quotient.mk (setoid h) (a + b) = Quotient.mk (setoid h) (c + d) := by
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

instance (h: M.sub β): Add (quotient h) := {
  add := λ x y ↦ Quotient.liftOn₂ x y _ (quotient_op h)
}

-- Show α / β is a commutative monoid.

instance LocalizationMonoid (α: Type u) (β: Set α) [M: CommMonoid α] (h: M.sub β): CommMonoid (quotient h) := {
  unit := Quotient.mk _ (0, ⟨0, h.unit_mem⟩)
  op := Add.add
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

-- Show if β = α (full set), then α / β is a group (group of differences).

def GroupOfDifferences (α: Type u) [M: CommMonoid α]: CommGroup (quotient M.full_sub) := {
  inv := by
    intro x
    apply Quotient.liftOn x (λ (a, b) => Quotient.mk _ (b, ⟨a, trivial⟩))
    intro (a₁, ⟨b₁, h₁⟩) (a₂, ⟨b₂, h₂⟩) ⟨t, ht₁, ht₂⟩
    simp
    apply Quotient.sound
    exists t
    constructor
    · trivial
    · calc
        b₁ + a₂ + t
        _ = a₂ + b₁ + t := by simp [op_comm]
        _ = a₁ + b₂ + t := by rw [ht₂]
        _ = b₂ + a₁ + t := by simp [op_comm]
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

end MonoidLocalization


variable {α: Type u} [R: CommRing α] {β: Set α}

-- Show if α is a ring, and β is a submonoid of the multiplicative monoid,
-- then α / β is a ring (localization of a commutative ring at β).

-- First, define operations

instance [h: R.toMulMonoid.sub β]: Zero (α × β) := {
  zero := (0, ⟨1, h.unit_mem⟩)
}

instance [h: R.toMulMonoid.sub β]: One (α × β) := {
  one := (1, ⟨1, h.unit_mem⟩)
}

instance [h: R.toMulMonoid.sub β]: Add (α × β) := {
  add := by
    intro (r₁, ⟨s₁, h₁⟩) (r₂, ⟨s₂, h₂⟩)
    have h: (s₁ * s₂) ∈ β := by apply h.op_closed s₁ s₂ h₁ h₂
    exact (r₁ * s₂ + r₂ * s₁, ⟨s₁ * s₂, h⟩)
}

instance: Neg (α × β) := {
  neg := by
    intro (r, s)
    exact (-r, s)
}

instance [h: R.toMulMonoid.sub β]: Mul (α × β) := {
  mul := add_pairs
}

-- Show the operations are well defined

theorem quotient_add (h: R.toMulMonoid.sub β): ∀ a b c d: (α × β), a ≈ c → b ≈ d → Quotient.mk (setoid h) (a + b) = Quotient.mk (setoid h) (c + d) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
  apply Quotient.sound
  exists t₁ * t₂
  constructor
  · apply h.op_closed
    · exact ht₁₁
    · exact ht₂₁
  · sorry

theorem quotient_neg (h: R.toMulMonoid.sub β): ∀ a b: (α × β), a ≈ b → Quotient.mk (setoid h) (-a) = Quotient.mk (setoid h) (-b) := by
  intro _ _ ⟨t, ht₁, ht₂⟩
  apply Quotient.sound
  exists t
  constructor
  · exact ht₁
  · sorry

-- Define instances

instance [h: R.toMulMonoid.sub β]: Zero (quotient h) := {
  zero := Quotient.mk _ 0
}

instance [h: R.toMulMonoid.sub β]: One (quotient h) := {
  one := Quotient.mk _ 1
}

instance [h: R.toMulMonoid.sub β]: Neg (quotient h) := {
  neg := λ x ↦ Quotient.liftOn x _ (quotient_neg h)
}

instance [h: R.toMulMonoid.sub β]: Add (quotient h) := {
  add := λ x y ↦ Quotient.liftOn₂ x y _ (quotient_add h)
}

instance [h: R.toMulMonoid.sub β]: Mul (quotient h) := {
  mul := λ x y ↦ Quotient.liftOn₂ x y _ (quotient_op h)
}

-- Finally, show it is a ring

def LocalizationOfRing [R: CommRing α] (h: R.toMulMonoid.sub β): CommRing (quotient h) := {
  one       := 1
  mul       := Mul.mul
  mul_assoc := (LocalizationMonoid α β h).assoc
  mul_comm  := (LocalizationMonoid α β h).comm
  mul_one   := (LocalizationMonoid α β h).identity
  zero := 0
  add := Add.add
  neg := Neg.neg
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
  add_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    apply Quotient.sound
    sorry
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
  add_neg := by
    constructor
    · intro x
      refine Quotient.inductionOn x ?_
      intro ⟨a₁, a₂⟩
      apply Quotient.sound
      sorry
    · sorry
  distrib := by
    constructor
    · intro x y z
      refine Quotient.inductionOn₃ x y z ?_
      intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩
      apply Quotient.sound
      sorry
    · sorry
}
