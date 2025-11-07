import Algae.RingTheory.Field
import Algae.SetTheory.Relation

open Ring

variable {R: Type u} [CommRing R] {S: Set R}

namespace Localization

-- Step 1: define the equivalence relation

def relation (S: Set R): Endorelation (R × S) :=
  λ (r₁, s₁) (r₂, s₂) ↦ ∃ t: R, t ∈ S ∧ t * (s₁ * r₂ - s₂ * r₁) = 0

theorem equivalence (hS: Submonoid S): Equivalence (relation S) := {
  refl := by
    intro (r, s)
    exists 1
    constructor
    · exact hS.unit_mem
    · rw [mul_one_left, sub_self]
  symm := by
    intro (r₁, s₁) (r₂, s₂) ⟨t, ht₁, ht₂⟩
    exists t
    constructor
    exact ht₁
    calc
      t * (s₂ * r₁ - s₁ * r₂)
      _ = t * (-(s₁ * r₂ - s₂ * r₁)) := by rw [neg_sub]
      _ = - (t * (s₁ * r₂ - s₂ * r₁)) := by rw [mul_neg]
      _ = - 0 := by rw [ht₂]
      _ = 0 := by rw [neg_zero]
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

def quotient (hS: Submonoid S): Type u :=
  Quotient ⟨relation S, equivalence hS⟩

-- TODO: lift the ring operations to the quotient,
-- i.e. show they are well defined..

-- TODO: show R/S is a ring

-- TODO define an integral domain

-- TODO: show if R is integral domain then R/S is field.
