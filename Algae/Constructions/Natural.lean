import Algae.RingTheory.Ring

/-

Construction of the natural numbers from scratch.

Want to show:
1. (additive structure)
  - commutative monoid wrt. addition
  - cancellative
2. (multiplicative structure)
  - commutative monoid wrt. multiplication
  - cancellative wrt. nonzero elements
(together 2 and 3 make a commutative semiring)
3. (order structure)
  - partial order: reflexive, transitive, antisymmetric
  - total
  - a lattice (has max/join and min/meet)
  - zero is a bottom element
  - every nonempty set has infimum
  - every set bounded above has supremum

Notes:
- Could use an ordered monoid with ⊥ = 0?

-/

inductive Natural where
| zero: Natural
| next: Natural → Natural

abbrev ℕ: Type :=
  Natural

namespace Natural

instance: Zero ℕ := ⟨zero⟩

def one: ℕ :=
  next zero

instance: One ℕ := ⟨one⟩

def add (a b: ℕ): ℕ :=
  match b with
  | zero => a
  | next p => next (add a p)

instance: Add ℕ := ⟨add⟩

-- Show (ℕ, +) is a cancellative commutative monoid.

theorem add_assoc (a b c: ℕ): a + b + c = a + (b + c) := by
  sorry

theorem add_zero_left (a: ℕ): 0 + a = a := by
  sorry

theorem add_zero_right (a: ℕ): a + 0 = a := by
  sorry

theorem add_comm (a b: ℕ): a + b = b + a := by
  sorry

theorem add_cancel_left {a b c: ℕ} (h: a + b = a + c): b = c := by
  sorry

theorem add_cancel_right {a b c: ℕ} (h: a + c = b + c): a = b := by
  sorry

theorem add_zero_eq_zero {a b: ℕ} (h: a + b = 0): a = 0 := by
  induction b with
  | zero => exact h
  | next p hp => contradiction

-- Show (ℕ, +) is a commutative monoid.

def mul (a b: ℕ): ℕ :=
  match b with
  | zero => zero
  | next p => add (mul a p) a

instance: Mul ℕ := ⟨mul⟩

theorem mul_assoc (a b c: ℕ): a * b * c = a * (b * c) := by
  sorry

theorem mul_one_left (a: ℕ): 1 * a = a := by
  sorry

theorem mul_one_right (a: ℕ): a * 1 = a := by
  sorry

theorem mul_comm (a b: ℕ): a * b = b * a := by
  sorry

theorem mul_cancel_left {a b c: ℕ} (h: a * b = a * c) (ha: a ≠ 0): b = c := by
  sorry

theorem mul_cancel_right {a b c: ℕ} (h: a + c = b + c) (hc: c ≠ 0): a = b := by
  sorry

-- Compatibility

theorem distrib_left (a b c: ℕ): a * (b + c) = a * b + a * c := by
  sorry

theorem distrib_right (a b c: ℕ): (a + b) * c = a * c + b * c := by
  sorry

theorem mul_zero_left (a: ℕ): 0 * a = 0 := by
  sorry

theorem mul_zero_right (a: ℕ): a * 0 = 0 := by
  sorry

def le (a b: ℕ): Prop :=
  ∃ d, a + d = b

instance: LE ℕ := ⟨le⟩

theorem le_refl (a: ℕ): a ≤ a := by
  exists 0

theorem le_trans {a b c: ℕ} (h₁: a ≤ b) (h₂: b ≤ c): a ≤ c := by
  obtain ⟨d₁, hd₁⟩ := h₁
  obtain ⟨d₂, hd₂⟩ := h₂
  exists d₁ + d₂
  rw [←hd₂, ←hd₁, add_assoc]

theorem le_antisymm {a b: ℕ} (h₁: a ≤ b) (h₂: b ≤ a): a = b := by
  obtain ⟨d₁, hd₁⟩ := h₁
  obtain ⟨d₂, hd₂⟩ := h₂
  have: a = a + (d₁ + d₂) := by calc
    a
    _ = b + d₂ := by rw [←hd₂]
    _ = a + d₁ + d₂ := by rw [←hd₁]
    _ = a + (d₁ + d₂) := by rw [add_assoc]
  have: d₁ + d₂ = 0 := by
    apply add_cancel_left (a := a)
    apply Eq.symm
    exact this
  have hd₁': d₁ = 0 := by
    exact add_zero_eq_zero this
  have hd₂': d₂ = 0 := by
    rw [add_comm] at this
    exact add_zero_eq_zero this
  rw [←hd₂, ←hd₁, hd₁', hd₂']
  repeat rw [add_zero_right]



theorem le_total (a b: ℕ): a ≤ b ∨ b ≤ a := by
  sorry

theorem le_bottom (a: ℕ): 0 ≤ a := by
  exists a
  exact add_zero_left a



-- TODO: is also cancellative monoid
instance NaturalSemiring: CommSemiring ℕ := {
  add := add
  zero := zero
  add_assoc := add_assoc
  add_zero := ⟨add_zero_left, add_zero_right⟩
  add_comm := add_comm
  mul := mul
  one := one
  mul_assoc := mul_assoc
  mul_one := ⟨mul_one_left, mul_one_right⟩
  distrib := ⟨distrib_left, distrib_right⟩
  mul_comm := sorry
}

-- TODO : prove is poset / lattice
