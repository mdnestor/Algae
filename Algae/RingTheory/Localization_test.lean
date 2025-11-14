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

Group of differences adds inverses to *all* elements of a commutative monoid.

Localization adds multiplicative inverses to *some* elements of a commutative
ring (which has a commutative monoid under multiplication).

So to generalize we need a construction that adds inverses to *some* elements
of a commutative monoid, where the "denominators" or "negatives" are taken from
some submonoid.

-/

variable {α: Type u} [M: CommMonoid α] {β: Set α}

open Monoid

-- Define the relation on α × β.

def relation (α: Type u) (β: Set α) [CommMonoid α]: α × β → α × β → Prop :=
  λ (a₁, ⟨b₁, _⟩) (a₂, ⟨b₂, _⟩) ↦ ∃ t ∈ β, a₁ + b₂ + t = a₂ + b₁ + t

/-
need to get this working

instance [Magma α]: Mul α := ⟨M.op⟩
instance [Pointed α]: One α := ⟨M.unit⟩

def relation (α: Type u) (β: Set α) [CommMonoid α]: α × β → α × β → Prop :=
  λ (a₁, b₁) (a₂, b₂) ↦ ∃ t ∈ β, a₁ * b₂ * t = a₂ * b₁ * t
-/

instance (α: Type u) (β: Set α) [CommMonoid α]: HasEquiv (α × β) := {
  Equiv := relation α β
}

-- Prove it is an equivalence relation.

theorem equivalence [h: M.sub β]: Equivalence (relation α β) := {
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

def setoid (α: Type u) (β: Set α) [M: CommMonoid α] [h: M.sub β]: Setoid (α × β) := {
  r := relation α β
  iseqv := equivalence
}

def quotient (α: Type u) (β: Set α) [M: CommMonoid α] [h: M.sub β]: Type u :=
  Quotient (setoid α β)

-- Lift the operation "add" to the quotient.

-- temp
namespace MonoidLocalize

def add_pairs [h: M.sub β]: (α × β) → (α × β) → (α × β) := by
    intro (a₁, ⟨b₁, h₁⟩) (a₂, ⟨b₂, h₂⟩)
    have h: (b₁ + b₂) ∈ β := by apply h.op_closed b₁ b₂ h₁ h₂
    exact (a₁ + a₂, ⟨b₁ + b₂, h⟩)

instance [h: M.sub β]: Add (α × β) := {
  add := add_pairs
}

theorem quotient_add [h: M.sub β]: ∀ a b c d: (α × β), a ≈ c → b ≈ d → Quotient.mk (setoid α β) (a + b) = Quotient.mk (setoid α β) (c + d) := by
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

instance [h: M.sub β]: Add (quotient α β) := {
  add := λ x y ↦ Quotient.liftOn₂ x y _ quotient_add
}

end MonoidLocalize

-- Show α / β is a commutative monoid.

instance LocalizationMonoid (α: Type u) (β: Set α) [M: CommMonoid α] (h: M.sub β): CommMonoid (quotient α β) := {
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

theorem full_set_submonoid (α: Type u) [M: Monoid α]: M.sub (Set.full α) := {
  unit_mem := trivial
  op_closed := by intros; trivial
}

def GroupOfDifferences (α: Type u) [M: CommMonoid α]: CommGroup (@quotient α (Set.full α) M (full_set_submonoid α)) := {
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
  mul := MonoidLocalize.add_pairs
}

-- Show the operations are well defined

theorem quotient_add [h: R.toMulMonoid.sub β]: ∀ a b c d: (α × β), a ≈ c → b ≈ d → Quotient.mk (setoid α β) (a + b) = Quotient.mk (setoid α β) (c + d) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
  apply Quotient.sound
  exists t₁ * t₂
  constructor
  · apply h.op_closed
    · exact ht₁₁
    · exact ht₂₁
  · sorry

theorem quotient_neg [h: R.toMulMonoid.sub β]: ∀ a b: (α × β), a ≈ b → Quotient.mk (setoid α β) (-a) = Quotient.mk (setoid α β) (-b) := by
  intro _ _ ⟨t, ht₁, ht₂⟩
  apply Quotient.sound
  exists t
  constructor
  · exact ht₁
  · sorry

-- Define instances

instance [h: R.toMulMonoid.sub β]: Zero (quotient α β) := {
  zero := Quotient.mk _ 0
}

instance [h: R.toMulMonoid.sub β]: One (quotient α β) := {
  one := Quotient.mk _ 1
}

instance [h: R.toMulMonoid.sub β]: Neg (quotient α β) := {
  neg := λ x ↦ Quotient.liftOn x _ quotient_neg
}

instance [h: R.toMulMonoid.sub β]: Add (quotient α β) := {
  add := λ x y ↦ Quotient.liftOn₂ x y _ quotient_add
}

instance [h: R.toMulMonoid.sub β]: Mul (quotient α β) := {
  mul := λ x y ↦ Quotient.liftOn₂ x y _ MonoidLocalize.quotient_add
}

-- Finally, show it is a ring

/-

This is completely unreadable because the equivalence is writen in terms of +,
so it is using + to mean the operation in the comm. monoid of the ring, and
also + to mean the addition in the ring

-/

def LocalizationOfRing (α: Type u) [R: CommRing α] (β: Set α) (h: R.toMulMonoid.sub β): CommRing (@quotient α β _ h) := {
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
    · sorry
  add_comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩
    apply Quotient.sound
    sorry
  add_zero := by
    constructor
    · intro x
      refine Quotient.inductionOn x ?_
      intro ⟨a₁, a₂⟩
      apply Quotient.sound
      sorry
    · sorry
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
