import Algae.RingTheory.Field
import Algae.SetTheory.Relation

open Ring

variable {R: Type u} [CommRing R] {S: Set R}

namespace Localization

/-

Localization of a ring:
- R is a commutative ring,
- S is a multiplicative closed subset (a submonoid in the multiplication of R)

Steps:
1. define the relation on R×S and show it is equivalence
2. show all the ring operations are well-defined in the quotient, hence can be lifted to R/S.
3. show R/S forms a ring.

-/

def MulClosed (S: Set R): Prop :=
  Ring.mul_struct.sub S


-- Step 1: define the equivalence relation

def r (S: Set R): Endorelation (R × S) :=
  λ (r₁, s₁) (r₂, s₂) ↦ ∃ t ∈ S, t * (s₁ * r₂ - s₂ * r₁) = 0

theorem r_equiv (h: MulClosed S): Equivalence (r S) := {
  refl := by
    intro (r, s)
    exists 1
    constructor
    · exact h.unit_mem
    · rw [mul_one_left, sub_self]
  symm := by
    intro (r₁, s₁) (r₂, s₂) ⟨t, ht₁, ht₂⟩
    exists t
    constructor
    exact ht₁
    calc
      t * (s₂ * r₁ - s₁ * r₂)
      _ = t * (-(s₁ * r₂ - s₂ * r₁)) := by rw [neg_sub]
      _ = - (t * (s₁ * r₂ - s₂ * r₁)) := by rw [mul_neg_right]
      _ = - 0 := by rw [ht₂]
      _ = 0 := by rw [neg_zero]
  trans := by
    intro (r₁, s₁) (r₂, s₂) (r₃, s₃) ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
    exists t₁ * t₂ * s₂
    constructor
    repeat apply h.op_closed
    exact ht₁₁
    exact ht₂₁
    exact s₂.property
    -- ht₁₂: t₁ * (s₁ * r₂ - s₂ * r₁) = 0
    -- ht₂₂: t₂ * (s₂ * r₃ - s₃ * r₂) = 0
    rw [distrib_sub_left]
    apply sub_zero_iff.mpr
    have: t₁ * s₁ * r₂ = t₁ * s₂ * r₁ := by
      apply sub_zero_iff.mp
      repeat rw [mul_assoc]
      rw [←distrib_sub_left]
      exact ht₁₂
    have: t₂ * s₂ * r₃ = t₂ * s₃ * r₂ := by
      apply sub_zero_iff.mp
      repeat rw [mul_assoc]
      rw [←distrib_sub_left]
      exact ht₂₂
    calc
      t₁ * t₂ * s₂ * (s₁ * r₃)
      _ = t₁ * t₂ * s₂ * (s₃ * r₁) := by sorry
}


instance (S: Set R): HasEquiv (R × S) := ⟨r S⟩

def setoid {S: Set R} (h: MulClosed S): Setoid (R × S) := {
  r := r S
  iseqv := r_equiv h
}

def quotient (h: MulClosed S): Type u :=
  Quotient (setoid h)

-- Define the operations/notation for 0, +, -, 1, * on the product.

instance: Zero (R × S) := {
  zero := sorry
}

instance: Add (R × S) := {
  add := sorry
}

instance: Neg (R × S) := {
  neg := sorry
}

instance: One (R × S) := {
  one := sorry
}

instance: Mul (R × S) := {
  mul := sorry
}

-- Step 2: show these operations are well defined in the quotient.

theorem quotient_add (h: MulClosed S) (a b c d: (R × S))
  (h₁: a ≈ c) (h₂: b ≈ d):
  Quotient.mk (setoid h) (a + b) = Quotient.mk (setoid h) (c + d) := by
  apply Quotient.sound
  -- Assumed a ≈ c and b ≈ d, so let t₁, t₂ be the corresponding elements in S.
  obtain ⟨t₁, ht₁₁, ht₁₂⟩ := h₁
  obtain ⟨t₂, ht₂₁, ht₂₂⟩ := h₂
  -- Then want to show a + b ≈ c + d via which t?
  let t: R := sorry
  exists t
  constructor
  -- t must belong to S
  sorry
  -- and must satisfy the corresponding equation t * (s₁ * r₂ - s₂ * r₁) = 0
  sorry

-- Similarly for neg and mul.

theorem quotient_neg (h₀: MulClosed S) (a b: (R × S))
  (h: a ≈ b):
  Quotient.mk (setoid h₀) (-a) = Quotient.mk (setoid h₀) (-b) := by
  apply Quotient.sound
  obtain ⟨t₁, ht₁₁, ht₁₂⟩ := h
  let t: R := sorry
  exists t
  constructor
  -- t must belong to S
  sorry
  -- and must satisfy the corresponding equation
  sorry

theorem quotient_mul (h: MulClosed S) (a b c d: (R × S))
  (h₁: a ≈ c) (h₂: b ≈ d):
  Quotient.mk (setoid h) (a * b) = Quotient.mk (setoid h) (c * d) := by
  apply Quotient.sound
  -- Assumed a ≈ c and b ≈ d, so let t₁, t₂ be the corresponding elements in S.
  obtain ⟨t₁, ht₁₁, ht₁₂⟩ := h₁
  obtain ⟨t₂, ht₂₁, ht₂₂⟩ := h₂
  -- Then want to show a + b ≈ c + d via which t?
  let t: R := sorry
  exists t
  constructor
  -- t must belong to S
  sorry
  -- and must satisfy the corresponding equation
  sorry


-- Now we can form instances of each on the quotient.
-- for the constants just use the quotient map.

instance (h: MulClosed S): Zero (quotient h) := {
  zero := Quotient.mk _ 0
}

instance (h: MulClosed S): One (quotient h) := {
  one := Quotient.mk _ 1
}

instance (h: MulClosed S): Neg (quotient h) := {
  neg := λ x ↦ Quotient.liftOn x _ (quotient_neg h)
}

instance (h: MulClosed S): Add (quotient h) := {
  add := λ x y ↦ Quotient.liftOn₂ x y _ (quotient_add h)
}

instance (h: MulClosed S): Mul (quotient h) := {
  mul := λ x y ↦ Quotient.liftOn₂ x y _ (quotient_mul h)
}

-- Step 3: show R/S is in fact a ring.

example (h: MulClosed S): CommRing (quotient h) := {
  add_struct := {
    unit := 0
    op := Add.add
    identity := sorry
    assoc := sorry
    inv := Neg.neg
    inverse := sorry
    comm := sorry
  }
  mul_struct := {
    unit := 1
    op := Mul.mul
    identity := sorry
    assoc := sorry
  }
  distrib := sorry
  mul_comm := sorry
}

-- TODO define an integral domain

-- TODO: show if R is integral domain then R/S is field.
