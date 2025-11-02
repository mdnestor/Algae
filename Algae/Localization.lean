import Algae.Ring
import Algae.Relation

variable {R: Type u}

-- Step 1: define the equivalence relation

def localization_relation [Ring R] (S: Set R): Endorelation (R × S) :=
  λ (r₁, s₁) (r₂, s₂) ↦ ∃ t: R, t ∈ S ∧ t * (s₁ * r₂ - s₂ * r₁) = 0

theorem localization_equivalence [Ring R] {S: Set R} (hS: @Submonoid R Ring.mul_struct S): Equivalence (localization_relation S) := {
  refl := by
    intro (r, s)
    exists 1
    constructor
    · exact hS.unit_mem
    · rw [Ring.mul_one_left, Ring.sub_self]
  symm := by
    intro (r₁, s₁) (r₂, s₂) ⟨t, ht₁, ht₂⟩
    exists t
    constructor
    exact ht₁
    calc
      t * (s₂ * r₁ - s₁ * r₂)
      _ = t * (-(s₁ * r₂ - s₂ * r₁)) := by rw [Ring.neg_sub]
      _ = - (t * (s₁ * r₂ - s₂ * r₁)) := by rw [Ring.mul_neg]
      _ = - 0 := by rw [ht₂]
      _ = 0 := by rw [Ring.neg_zero]
  trans := by
    intro (r₁, s₁) (r₂, s₂) (r₃, s₃) ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
    exists t₁ * t₂ * s₂
    constructor
    repeat apply hS.op_closed
    exact ht₁₁
    exact ht₂₁
    exact s₂.property
    -- ht₁₂ : t₁ * (s₁ * r₂ - s₂ * r₁) = 0
    -- ht₂₂ : t₂ * (s₂ * r₃ - s₃ * r₂) = 0
    rw [Ring.distrib_sub_left]
    apply Ring.sub_zero_iff.mpr
    have: t₁ * s₁ * r₂ = t₁ * s₂ * r₁ := by
      apply Ring.sub_zero_iff.mp
      repeat rw [Ring.mul_assoc]
      rw [←Ring.distrib_sub_left]
      exact ht₁₂
    have: t₂ * s₂ * r₃ = t₂ * s₃ * r₂ := by
      apply Ring.sub_zero_iff.mp
      repeat rw [Ring.mul_assoc]
      rw [←Ring.distrib_sub_left]
      exact ht₂₂
    calc
      t₁ * t₂ * s₂ * (s₁ * r₃)
      _ = t₁ * t₂ * s₂ * (s₃ * r₁) := by sorry
}

def localization_quotient [Ring R] {S: Set R} (hS: @Submonoid R Ring.mul_struct S): Type u :=
  Quotient ⟨localization_relation S, localization_equivalence hS⟩

-- TODO: lift the ring operations to the quotient,
-- i.e. show they are well defined..

-- TODO: show R/S is a ring

-- TODO: show if R is integral domain then R/S is field.
