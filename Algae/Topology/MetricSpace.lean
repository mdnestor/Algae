import Algae.SetTheory.Relation
import Algae.GroupTheory.Monoid

variable {X: Type u} {D: Type v}

open Monoid



/-

A (generalized) metric space consists of

- a set X
- a set D with "distance space" structure: ordering ≤, bottom ⊥, addition +.
- a function d: X × X → D
- d(x, y) = ⊥ ↔ x = y
- d(x, y) = d(y, x)
- Triangle inequality: d(x, z) ≤ d(x, y) + d(x, z)

-/


class DistanceSpace (D: Type v) where
  le: D → D → Prop
  bottom: D
  bottom_le: ∀ x, le bottom x
  add: D → D → D
  add_assoc: Associative add
  add_bottom: Identity add bottom

instance [DistanceSpace D]: Bottom D := {
  le := DistanceSpace.le
  bottom := DistanceSpace.bottom
  bottom_le := DistanceSpace.bottom_le
}

instance [DistanceSpace D]: Monoid D := {
  op := DistanceSpace.add
  unit := DistanceSpace.bottom
  identity := DistanceSpace.add_bottom
  assoc := DistanceSpace.add_assoc
}

-- In a distance space, the bottom element is the zero in the monoid by definition.
theorem DistanceSpace.bottom_eq_zero [DistanceSpace D]: (⊥: D) = 0 := by
  rfl

-- Real numbers placeholder in case special cases needed
-- this should eventually move somewhere else
-- (until we actually construct it)
axiom ℝ: Type

instance: DistanceSpace ℝ := sorry



-- Metric space

class Metric (X: Type u) (D: Type v) [DistanceSpace D] where
  distance: X → X → D
  distance_bot_iff: ∀ x y, distance x y = ⊥ ↔ x = y
  distance_symm: ∀ x y, distance x y = distance y x
  distance_triangle: ∀ x y z, distance x z ≤ distance x y + distance y z

instance [DistanceSpace D] [Metric X D]: CoeFun (Metric X D) (λ _ ↦ X → X → D) := {
  coe _ := Metric.distance
}

variable [DistanceSpace D]

-- Unpack metric axioms

theorem distance_bot_iff [d: Metric X D]: ∀ x y, d x y = ⊥ ↔ x = y := by
  exact Metric.distance_bot_iff

theorem distance_symm [d: Metric X D]: ∀ x y, d x y = d y x := by
  exact Metric.distance_symm

theorem distance_triangle [d: Metric X D]: ∀ x y z, d x z ≤ d x y + d y z := by
  exact Metric.distance_triangle

theorem dist_self_bot [d: Metric X D] (x: X): d x x = ⊥ := by
  apply (distance_bot_iff x x).mpr
  rfl



-- Sequences

def Sequence (X: Type u): Type u :=
  Nat → X

def ConvergesTo (d: Metric X D) (a: Sequence X) (x: X): Prop :=
  ∀ r, ⊥ < r → ∃ n, ∀ m, n ≤ m → d (a m) x < r

def Convergent (d: Metric X D) (a: Sequence X): Prop :=
  ∃ x, ConvergesTo d a x

-- optional: define the limit of a convergent sequence via choose

theorem constant_sequence_converges (d: Metric X D) (x: X): ConvergesTo d (λ _ ↦ x) x := by
  intro r hr
  exists 0
  intros
  rw [dist_self_bot]
  exact hr

def tail (s: Sequence X) (t: Nat): Sequence X :=
  λ n ↦ s (n + t)

theorem converges_iff_tails_converge (d: Metric X D) (a: Sequence X) (x: X): ConvergesTo d a x ↔ ∀ t, ConvergesTo d (tail a t) x := by
  constructor
  · intro h t r hr
    obtain ⟨n, hn⟩ := h r hr
    exists n - t
    intro m hm
    apply hn (m + t)
    exact Nat.le_add_of_sub_le hm
  · intro h
    exact h 0

theorem converges_iff_tail_converges (d: Metric X D) (a: Sequence X) (x: X): ConvergesTo d a x ↔ ∃ t, ConvergesTo d (tail a t) x := by
  constructor
  · intro h
    exists 0
  · intro ⟨t, ht⟩ r hr
    have ⟨n, hn⟩ := ht r hr
    exists n + t
    intro m hm
    simp [tail] at hn
    have := hn (m - t) (Nat.le_sub_of_add_le hm)
    rw [Nat.sub_add_cancel (Nat.le_of_add_left_le hm)] at this
    exact this

theorem not_lt_self (x: D): ¬(x < x) := by
  exact Std.Irrefl.irrefl x

theorem le_antisymm {x₁ x₂: D}: x₁ ≤ x₂ → x₂ ≤ x₁ → x₁ = x₂ := by
  sorry

theorem le_add {x₁ x₂ y₁ y₂: D} (h₁: x₁ < y₁) (h₂: x₂ < y₂): x₁ + x₂ < y₁ + y₂ := by
  sorry

theorem le_lt_trans {x y z: D} (h₁: x ≤ y) (h₂: y < z): x < z := by
  sorry

theorem not_lt {x y: D}: ¬x < y ↔ y ≤ x := by
  sorry

theorem eq_bot_iff (x₀: D): x₀ = ⊥ ↔ ∀ x, ⊥ < x → x₀ < x := by
  constructor
  · intro h _ hx
    exact lt_of_eq_of_lt h hx
  · intro h
    have h' := h x₀
    by_cases hx: ⊥ < x₀
    · have := h' hx
      have := not_lt_self x₀
      contradiction
    · have hx₀: x₀ ≤ ⊥ := by exact not_lt.mp hx
      have hx: ∀ x: D, ⊥ ≤ x := by exact Bottom.bottom_le
      have hx₀':= hx x₀
      exact le_antisymm hx₀ hx₀'

theorem limit_unique {d: Metric X D} {a: Sequence X} {x₁ x₂: X} (h₁: ConvergesTo d a x₁) (h₂: ConvergesTo d a x₂): x₁ = x₂ := by
  apply (d.distance_bot_iff x₁ x₂).mp
  apply (eq_bot_iff (d x₁ x₂)).mpr
  intro r₀ hr₀
  ------- need r = r₀ / 2 -------
  have r: D := sorry
  have hr: ⊥ < r := sorry
  have hr': r₀ = r + r := sorry
  -------------------------------
  rw [hr']
  have ⟨n₁, hn₁⟩ := h₁ r hr
  have ⟨n₂, hn₂⟩ := h₂ r hr
  by_cases h: n₁ ≤ n₂
  · have dx₁ := (hn₁ n₂ h)
    have dx₂ := (hn₂ n₂ (Nat.le_refl n₂))
    rw [distance_symm] at dx₁
    have := le_add dx₁ dx₂
    exact (le_lt_trans (d.distance_triangle x₁ (a n₂) x₂) this)
  · have dx₂ := (hn₂ n₁ (Nat.le_of_not_ge h))
    have dx₁ := (hn₁ n₁ (Nat.le_refl n₁))
    rw [distance_symm] at dx₂ ⊢
    have := le_add dx₂ dx₁
    exact (le_lt_trans (d.distance_triangle x₂ (a n₁) x₁) this)



-- Open and closed balls

def OpenBall (d: Metric X D) (x₀: X) (r: D): Set X :=
  λ x ↦ d x₀ x < r

def ClosedBall (d: Metric X D) (x₀: X) (r: D): Set X :=
  λ x ↦ d x₀ x ≤ r

def Sphere (d: Metric X D) (x₀: X) (r: D): Set X :=
  λ x ↦ d x₀ x = r

-- Open set

def is_open_set (d: Metric X D) (S: Set X): Prop :=
  ∀ x, S x → ∃ r, OpenBall d x r ⊆ S

/-
  TODO:
  - monotone ball inclusion
  - boundedness
-/

-- Cauchy

def cauchy (d: Metric X D) (a: Sequence X): Prop :=
  ∀ r, 0 < r → ∃ N, ∀ m n, N ≤ m → N ≤ n → d (a m) (a n) < r
