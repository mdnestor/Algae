import Algae.GroupTheory.Group

/-

Construction of the group of difference of a commutative monoid, aka the Grothendeick group.
https://en.wikipedia.org/wiki/Grothendieck_group

E.g. how the integers are constructed from the naturals.

-/

variable {α: Type u}

namespace DifferenceGroup

open Group

def relation (α: Type u) [Magma α]: α × α → α × α → Prop :=
  λ (a₁, a₂) (b₁, b₂) ↦ ∃ k, a₁ + b₂ + k = b₁ + a₂ + k

instance(α: Type u) [Magma α]: HasEquiv (α × α) := {
  Equiv := relation α
}

theorem equivalence [CommMonoid α]: Equivalence (relation α) := {
  refl := by
    intro
    exists 0
  symm := by
    intro _ _ ⟨k, hk⟩
    exists k
    exact (Eq.symm hk)
  trans := by
    intro (x₁, x₂) (y₁, y₂) (z₁, z₂) ⟨k₁, hk₁⟩ ⟨k₂, hk₂⟩
    exists y₁ + y₂ + k₁ + k₂
    calc
      x₁ + z₂ + (y₁ + y₂ + k₁ + k₂)
      _ = (x₁ + y₂ + k₁) + (y₁ + z₂ + k₂) := by sorry -- tedious, not sure how to automate?
      _ = (y₁ + x₂ + k₁) + (z₁ + y₂ + k₂) := by rw [hk₁, hk₂]
      _ = z₁ + x₂ + (y₁ + y₂ + k₁ + k₂) := by sorry
}

def setoid (α: Type u) [CommMonoid α]: Setoid (α × α) := {
  r := relation α
  iseqv := equivalence
}

def quotient (α: Type u) [CommMonoid α]: Type u :=
  Quotient (setoid α)

-- Part 2: lift the addition operation to the quotient.

instance (α: Type u) [Zero α]: Zero (α × α) := {
  zero := (0, 0)
}

instance [CommMonoid α]: Zero (quotient α) := {
  zero := Quotient.mk _ 0
}

instance (α: Type u) [Add α]: Add (α × α) := {
  add := λ (x₁, x₂) (y₁, y₂) ↦ (x₁ + y₁, x₂ + y₂)
}

theorem quotient_add [CommMonoid α] (a b c d: α × α) (h₁: a ≈ c) (h₂: b ≈ d):
  Quotient.mk (setoid α) (a + b) = Quotient.mk (setoid α) (c + d) := by
  apply Quotient.sound
  obtain ⟨k₁, hk₁⟩ := h₁
  obtain ⟨k₂, hk₂⟩ := h₂
  exists k₁ + k₂
  calc
    a.fst + b.fst + (c.snd + d.snd) + (k₁ + k₂)
    _ = (a.fst + c.snd + k₁) + (b.fst + d.snd + k₂) := by sorry
    _ = (c.fst + a.snd + k₁) + (d.fst + b.snd + k₂) := by rw [hk₁, hk₂]
    _ = c.fst + d.fst + (a.snd + b.snd) + (k₁ + k₂) := by sorry

instance [CommMonoid α]: Add (quotient α) := {
  add := λ x y ↦ Quotient.liftOn₂ x y _ quotient_add
}

theorem quotient_neg [CommMonoid α] (a b: α × α) (h: a ≈ b):
  Quotient.mk (setoid α) (Prod.swap a) = Quotient.mk (setoid α) (Prod.swap b) := by
  apply Quotient.sound
  obtain ⟨k, hk⟩ := h
  exists k
  calc
    a.snd + b.fst + k
    _ = b.fst + a.snd + k := by rw [op_comm a.snd]
    _ = a.fst + b.snd + k := by rw [hk]
    _ = b.snd + a.fst + k := by rw [op_comm a.fst]

instance [CommMonoid α]: Neg (quotient α) := {
  neg := λ x ↦ Quotient.liftOn x _ quotient_neg
}

-- Step 3: show the quotient forms a commutative group.
-- The add, zero, and neg instances are automatically inferred
-- based on the above constructions.

instance DifferenceGroup [CommMonoid α]: CommGroup (quotient α) := {
  unit := Zero.zero
  op := Add.add
  inv := Neg.neg -- TODO not right
  assoc := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intros
    apply Quotient.sound
    exists 0
    simp [op_assoc]
  identity := by
    constructor <;> (
      intro x
      refine Quotient.inductionOn x ?_
      intro
      apply Quotient.sound
      exists 0
    )
    repeat rw [op_unit_left]
    repeat rw [op_unit_right]
  inverse := by
    constructor <;> (
      intro x
      refine Quotient.inductionOn x ?_
      intro
      apply Quotient.sound
      exists 0
      simp [op_comm]
    )
  comm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intros
    apply Quotient.sound
    exists 0
    simp [op_comm]
}
