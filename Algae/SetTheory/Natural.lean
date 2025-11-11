/-

Construction of the natural numbers from scratch.

TODO: some of these properties hold in general semiring.

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

-- Show (ℕ, +) is a commutative monoid.

def mul (a b: ℕ): ℕ :=
  match b with
  | zero => zero
  | next p => next (add a p)

instance: Mul ℕ := ⟨mul⟩

theorem mul_assoc (a b c: ℕ): a * b * c = a * (b * c) := by
  sorry

theorem mul_one_left (a: ℕ): 1 * a = a := by
  sorry

theorem mul_one_right (a: ℕ): a * 1 = a := by
  sorry

theorem mul_comm (a b: ℕ): a + b = b + a := by
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
  ∃ c, a + c = b

instance: LE ℕ := ⟨le⟩

theorem le_refl (a: ℕ): a ≤ a := by
  exists 0

theorem le_trans {a b c: ℕ} (h₁: a ≤ b) (h₂: b ≤ c): a ≤ c := by
  sorry

theorem le_total (a b: ℕ): a ≤ b ∨ b ≤ a := by
  sorry
