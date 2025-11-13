import Algae.RingTheory.Field
import Algae.SetTheory.Relation

variable {R: Type u} [𝓡: CommRing R] {S: Set R}

open Ring
namespace Localization

/-

Localization of a ring requires:
- R, a commutative ring
- S, a multiplicative subset (a submonoid in the multiplication of R)

Steps:
1. define the relation on R × S and show it is an equivalence relation.
2. show the operations are well-defined in the quotient, and hence can be lifted to R/S.
3. show R/S forms a ring.

-/


-- Step 1: define the equivalence relation

def relation (S: Set R): Endorelation (R × S) :=
  λ (r₁, s₁) (r₂, s₂) ↦ ∃ t ∈ S, t * (s₁ * r₂ - s₂ * r₁) = 0

theorem equivalence [h: 𝓡.toMulMonoid.sub S]: Equivalence (relation S) := {
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
    · exact ht₁
    · calc
      t * (s₂ * r₁ - s₁ * r₂)
      _ = t * (-(s₁ * r₂ - s₂ * r₁)) := by rw [neg_sub]
      _ = - (t * (s₁ * r₂ - s₂ * r₁)) := by rw [mul_neg_right]
      _ = - 0 := by rw [ht₂]
      _ = 0 := by rw [neg_zero]
  trans := by
    intro (r₁, s₁) (r₂, s₂) (r₃, s₃) ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
    exists t₁ * t₂ * s₂
    constructor
    · repeat apply h.op_closed
      · exact ht₁₁
      · exact ht₂₁
      · exact s₂.property
    · rw [distrib_sub_left]
      apply sub_zero_iff.mpr
      have h₃: t₁ * s₁ * r₂ = t₁ * s₂ * r₁ := by
        apply sub_zero_iff.mp
        repeat rw [mul_assoc]
        rw [←distrib_sub_left]
        exact ht₁₂
      have h₄: t₂ * s₂ * r₃ = t₂ * s₃ * r₂ := by
        apply sub_zero_iff.mp
        repeat rw [mul_assoc]
        rw [←distrib_sub_left]
        exact ht₂₂
      calc
        t₁ * t₂ * s₂ * (s₁ * r₃)
        _ = t₁ * t₂ * s₂ * (r₃ * s₁)     := by simp [mul_comm]
        _ = t₁ * (t₂ * s₂ * r₃) * s₁     := by simp [mul_assoc]
        _ = t₁ * (t₂ * s₃ * r₂) * s₁     := by rw [h₄]
        _ = t₁ * (((t₂ * s₃) * r₂) * s₁) := by rw [mul_assoc]
        _ = t₁ * (s₁ * (r₂ * (t₂ * s₃))) := by simp [mul_comm]
        _ = t₁ * s₁ * r₂ * t₂ * s₃       := by simp [mul_assoc]
        _ = t₁ * s₂ * r₁ * t₂ * s₃       := by rw [h₃]
        _ = t₁ * (s₂ * (r₁ * (t₂ * s₃))) := by simp [mul_assoc]
        _ = t₁ * (((t₂ * s₃) * r₁) * s₂) := by simp [mul_comm]
        _ = t₁ * t₂ * ((s₃ * r₁) * s₂)   := by simp [mul_assoc]
        _ = t₁ * t₂ * (s₂ * (s₃ * r₁))   := by simp [mul_comm]
        _ = t₁ * t₂ * s₂ * (s₃ * r₁)     := by simp [mul_assoc]
}

instance (S: Set R): HasEquiv (R × S) := ⟨relation S⟩

def setoid [h: 𝓡.toMulMonoid.sub S]: Setoid (R × S) := {
  r := relation S
  iseqv := equivalence
}

def quotient (h: 𝓡.toMulMonoid.sub S): Type u :=
  Quotient (@setoid R _ S h)

-- Define 0, 1, +, -, and * on the product.

instance [h: 𝓡.toMulMonoid.sub S]: Zero (R × S) := {
  zero := (0, ⟨1, h.unit_mem⟩)
}

instance [h: 𝓡.toMulMonoid.sub S]: Add (R × S) := {
  add := by
    intro (r₁, ⟨s₁, h₁⟩) (r₂, ⟨s₂, h₂⟩)
    have h: (s₁ * s₂) ∈ S := by apply h.op_closed s₁ s₂ h₁ h₂
    exact (r₁ * s₂ + r₂ * s₁, ⟨s₁ * s₂, h⟩)
}

instance: Neg (R × S) := {
  neg := by
    intro (r, s)
    exact (-r, s)
}

instance [h: 𝓡.toMulMonoid.sub S]: One (R × S) := {
  one := (1, ⟨1, h.unit_mem⟩)
}

instance [h: 𝓡.toMulMonoid.sub S]: Mul (R × S) := {
  mul := by
    intro (r₁, ⟨s₁, h₁⟩) (r₂, ⟨s₂, h₂⟩)
    have h: (s₁ * s₂) ∈ S := by apply h.op_closed s₁ s₂ h₁ h₂
    exact (r₁ * r₂, ⟨s₁ * s₂, h⟩)
}

-- Step 2: show these operations are well defined in the quotient.

theorem quotient_add [h: 𝓡.toMulMonoid.sub S]: ∀ a b c d: (R × S), a ≈ c → b ≈ d → Quotient.mk setoid (a + b) = Quotient.mk setoid (c + d) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
  apply Quotient.sound
  exists t₁ * t₂
  constructor
  · apply h.op_closed
    · exact ht₁₁
    · exact ht₂₁
  · rw [distrib_sub_left] at ht₁₂ ht₂₂ ⊢
    rw [sub_zero_iff] at ht₁₂ ht₂₂ ⊢
    repeat rw [distrib_left]
    -- math is beautiful
    calc
      _ = (t₁ * (t₂ * (a₂ * (b₂ * c₁))) * d₂) + (t₁ * (t₂ * (a₂ * (b₂ * d₁))) * c₂) := by simp [mul_assoc]
      _ = (t₁ * ((a₂ * (c₁ * b₂)) * t₂) * d₂) + ((t₂ * ((b₂ * d₁) * a₂)) * t₁ * c₂) := by simp [mul_comm]
      _ = ((t₁ * (a₂ * c₁)) * b₂ * t₂ * d₂) + ((t₂ * (b₂ * d₁)) * a₂ * t₁ * c₂)     := by simp [mul_assoc]
      _ = ((t₁ * (c₂ * a₁)) * b₂ * t₂ * d₂) + ((t₂ * (d₂ * b₁)) * a₂ * t₁ * c₂)     := by simp [ht₁₂, ht₂₂]
      _ = t₁ * ((c₂ * (a₁ * b₂)) * t₂) * d₂ + ((t₂ * (d₂ * b₁ * a₂)) * t₁) * c₂     := by simp [mul_assoc]
      _ = t₁ * (t₂ * (c₂ * (b₂ * a₁))) * d₂ + (t₁ * (t₂ * (d₂ * b₁ * a₂))) * c₂     := by simp [mul_comm]
      _ = t₁ * t₂ * c₂ * ((b₂ * a₁) * d₂) + t₁ * t₂ * ((d₂ * b₁ * a₂) * c₂)         := by simp [mul_assoc]
      _ = t₁ * t₂ * c₂ * (d₂ * (a₁ * b₂)) + t₁ * t₂ * (c₂ * (d₂ * b₁ * a₂))         := by simp [mul_comm]
      _ = (t₁ * t₂ * (c₂ * d₂ * (a₁ * b₂)) + t₁ * t₂ * (c₂ * d₂ * (b₁ * a₂)))       := by simp [mul_assoc]

theorem quotient_neg [h: 𝓡.toMulMonoid.sub S]: ∀ a b: (R × S), a ≈ b → Quotient.mk setoid (-a) = Quotient.mk setoid (-b) := by
  intro _ _ ⟨t, ht₁, ht₂⟩
  apply Quotient.sound
  exists t
  constructor
  · exact ht₁
  · rw [distrib_sub_left] at ht₂ ⊢
    rw [sub_zero_iff] at ht₂ ⊢
    repeat rw [mul_neg_right]
    rw [ht₂]

theorem quotient_mul [h: 𝓡.toMulMonoid.sub S]: ∀ a b c d: (R × S), a ≈ c → b ≈ d → Quotient.mk setoid (a * b) = Quotient.mk setoid (c * d) := by
  intro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ ⟨c₁, c₂⟩ ⟨d₁, d₂⟩ ⟨t₁, ht₁₁, ht₁₂⟩ ⟨t₂, ht₂₁, ht₂₂⟩
  apply Quotient.sound
  exists t₁ * t₂
  constructor
  · apply h.op_closed
    · exact ht₁₁
    · exact ht₂₁
  · rw [distrib_sub_left] at ht₁₂ ht₂₂ ⊢
    rw [sub_zero_iff] at ht₁₂ ht₂₂ ⊢
    repeat rw [distrib_left]
    calc
    t₁ * t₂ * (a₂ * b₂ * (c₁ * d₁))
    _ = t₁ * (t₂ * (a₂ * (b₂ * c₁))) * d₁   := by simp [mul_assoc]
    _ = t₁ * ((a₂ * (c₁ * b₂)) * t₂) * d₁   := by simp [mul_comm]
    _ = (t₁ * a₂ * c₁) * (b₂ * t₂ * d₁)     := by simp [mul_assoc]
    _ = (t₁ * a₂ * c₁) * (t₂ * b₂ * d₁)     := by simp [mul_comm]
    _ = (t₁ * (a₂ * c₁)) * (t₂ * (b₂ * d₁)) := by simp [mul_assoc]
    _ = (t₁ * (c₂ * a₁)) * (t₂ * (d₂ * b₁)) := by simp [ht₁₂, ht₂₂]
    _ = t₁ * ((c₂ * a₁) * t₂) * d₂ * b₁     := by simp [mul_assoc]
    _ = t₁ * (t₂ * (c₂ * a₁)) * d₂ * b₁     := by simp [mul_comm]
    _ = t₁ * t₂ * c₂ * ((a₁ * d₂) * b₁)     := by simp [mul_assoc]
    _ = t₁ * t₂ * c₂ * ((d₂ * a₁) * b₁)     := by simp [mul_comm]
    _ = t₁ * t₂ * (c₂ * d₂ * (a₁ * b₁))     := by simp [mul_assoc]


-- Now we can form instances of each on the quotient.
-- for the constants just use the quotient map.

instance [h: 𝓡.toMulMonoid.sub S]: Zero (quotient h) := {
  zero := Quotient.mk _ 0
}

instance [h: 𝓡.toMulMonoid.sub S]: One (quotient h) := {
  one := Quotient.mk _ 1
}

instance [h: 𝓡.toMulMonoid.sub S]: Neg (quotient h) := {
  neg := λ x ↦ Quotient.liftOn x _ quotient_neg
}

instance [h: 𝓡.toMulMonoid.sub S]: Add (quotient h) := {
  add := λ x y ↦ Quotient.liftOn₂ x y _ quotient_add
}

instance [h: 𝓡.toMulMonoid.sub S]: Mul (quotient h) := {
  mul := λ x y ↦ Quotient.liftOn₂ x y _ quotient_mul
}

-- Step 3: show R/S is a ring.

instance LocalizationRing (h: 𝓡.toMulMonoid.sub S): CommRing (quotient h) := {
  add := Add.add
  zero := 0
  add_assoc := sorry
  add_zero := sorry
  add_comm := sorry
  mul := Mul.mul
  one := 1
  mul_assoc := sorry
  mul_one := sorry
  distrib := sorry
  neg := sorry
  add_neg := sorry
  mul_comm := sorry
}

-- TODO: show j: r ↦ r/1 is a ring homomprhism, and injective iff. S does not contain zero divisors

-- TODO: show 0 ∈ S iff. R/S is the zero ring

-- TODO: integral domain and field of fractions
def NoZeroDivisors (R: Type u) [Semiring R]: Prop :=
  ∀ a b: R, a ≠ 0 → b ≠ 0 → a * b ≠ 0

def Nonzero (R: Type u) [Semiring R]: Prop :=
  (0: R) ≠ Semiring.one

def IntegralDomain (R: Type u) [CommRing R]: Prop :=
  Nonzero R ∧ NoZeroDivisors R

theorem nonzero_mul_closed {R: Type u} [𝓡: CommRing R] (h: IntegralDomain R): 𝓡.toMulMonoid.sub (λ r ↦ r ≠ 0) := {
  unit_mem := Ne.symm h.left
  op_closed := h.right
}

def FieldOfFractions {R: Type u} [CommRing R] (h: IntegralDomain R): Field (quotient (nonzero_mul_closed h)) := {
  add       := (LocalizationRing (nonzero_mul_closed h)).add
  zero      := (LocalizationRing (nonzero_mul_closed h)).zero
  add_assoc := (LocalizationRing (nonzero_mul_closed h)).add_assoc
  add_zero  := (LocalizationRing (nonzero_mul_closed h)).add_zero
  add_comm  := (LocalizationRing (nonzero_mul_closed h)).add_comm
  mul       := (LocalizationRing (nonzero_mul_closed h)).mul
  one       := (LocalizationRing (nonzero_mul_closed h)).one
  mul_assoc := (LocalizationRing (nonzero_mul_closed h)).mul_assoc
  mul_one   := (LocalizationRing (nonzero_mul_closed h)).mul_one
  distrib   := (LocalizationRing (nonzero_mul_closed h)).distrib
  neg       := (LocalizationRing (nonzero_mul_closed h)).neg
  add_neg   := (LocalizationRing (nonzero_mul_closed h)).add_neg
  mul_comm  := (LocalizationRing (nonzero_mul_closed h)).mul_comm
  inv := sorry
  mul_inverses := sorry
}
