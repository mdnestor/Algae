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

TODO: Switch sequences from Nat to ℕ.

-/

class DistanceSpace (D: Type v) where
  le: D → D → Prop
  le_refl: ∀ d, le d d
  le_trans: ∀ d₁ d₂ d₃, le d₁ d₂ → le d₂ d₃ → le d₁ d₃
  le_antisymm: ∀ d₁ d₂, le d₁ d₂ → le d₂ d₁ → d₁ = d₂
  bottom: D
  bottom_le: ∀ x, le bottom x
  add: D → D → D
  add_assoc: Associative add
  add_bottom: Identity add bottom
  le_add: ∀ d₁ d₂ d, le d₁ d₂ ↔ le (add d₁ d) (add d₂ d)

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

def DistanceComplete (D: Type v) [DistanceSpace D]: Prop :=
  ∀ d: D, ⊥ < d → ∃ r, ⊥ < r ∧ r + r ≤ d

-- In a distance space, the bottom element is the zero in the monoid by definition.
theorem DistanceSpace.bottom_eq_zero [DistanceSpace D]: (⊥: D) = 0 := by
  rfl

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

theorem le_add {x₁ x₂ y₁ y₂: D} (h₁: x₁ < y₁) (h₂: x₂ < y₂): x₁ + x₂ < y₁ + y₂ := by
  sorry

theorem le_lt_trans {x y z: D} (h₁: x ≤ y) (h₂: y < z): x < z := by
  sorry

theorem lt_le_trans {x y z: D} (h₁: x < y) (h₂: y ≤ z): x < z := by
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
      exact DistanceSpace.le_antisymm _ _ hx₀ hx₀'

theorem limit_unique {d: Metric X D} {a: Sequence X} {x₁ x₂: X} (h₀: DistanceComplete D) (h₁: ConvergesTo d a x₁) (h₂: ConvergesTo d a x₂): x₁ = x₂ := by
  apply (d.distance_bot_iff x₁ x₂).mp
  apply (eq_bot_iff (d x₁ x₂)).mpr
  intro r₀ hr₀
  ------- need r = r₀ / 2 -------
  obtain ⟨r, hr₁, hr₂⟩ := h₀ r₀ hr₀
  have r: D := sorry
  have hr₁: ⊥ < r := sorry
  have hr₂: r₀ = r + r := sorry
  -------------------------------
  rw [hr₂]
  have ⟨n₁, hn₁⟩ := h₁ r hr₁
  have ⟨n₂, hn₂⟩ := h₂ r hr₁
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

theorem OpenBall.empty (d: Metric X D) (x₀: X): OpenBall d x₀ ⊥ = Set.empty := by
  funext x; simp
  constructor
  · intro ⟨_, _⟩
    have := DistanceSpace.bottom_le (d x₀ x)
    contradiction
  · intro
    contradiction

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
  - continuous functions:
    - constant, identity, composition are continuous
  - Product metric

-/





-- Cauchy sequence

def Cauchy (d: Metric X D) (a: Sequence X): Prop :=
  ∀ r, ⊥ < r → ∃ N, ∀ m n, N ≤ m → N ≤ n → d (a m) (a n) < r

theorem cauchy_if_convergent (h₀: DistanceComplete D) {d: Metric X D} {a: Sequence X} (h: Convergent d a): Cauchy d a := by
  intro r₀ hr₀
  have ⟨x, hx⟩ := h
  have ⟨r, hr₁, hr₂⟩ := h₀ r₀ hr₀
  have ⟨N, hN⟩ := hx r hr₁
  exists N
  intro m n hm hn
  have dm := hN m hm
  have dn := hN n hn
  rw [d.distance_symm] at dn
  have := le_lt_trans (d.distance_triangle (a m) x (a n)) (le_add dm dn)
  exact lt_le_trans this hr₂

def Complete (d: Metric X D): Prop :=
  ∀ a, Cauchy d a → Convergent d a

-- Given a metric space (X, d) we can build a complete metric space
-- via the quotient on the set of Cauchy sequences
-- by that the relation that their difference converges to zero.
-- i.e. given two cauchy sequences a(n) b(n)
-- a ~ b if d(a(n), b(n)) -> 0.

abbrev Endometric (D: Type u) [DistanceSpace D]: Type u :=
  Metric D D

def CauchyRelation (d₀: Endometric D) (d: Metric X D): Endorelation (Sequence X) :=
  λ a b ↦ ConvergesTo d₀ (λ n ↦ d (a n) (b n)) ⊥

def Endometric.obedient (d₀: Endometric D): Prop :=
  ∀ r, d₀ r ⊥ = r

theorem CauchyRelation.equiv (hd: DistanceComplete D) (d₀: Endometric D) (hd₀: d₀.obedient) (d: Metric X D): Equivalence (CauchyRelation d₀ d) := {
  refl := by
    intro _ _ hr
    exists 321
    intro _ _
    simp [dist_self_bot]
    exact hr
  symm := by
    intro _ _ h r hr
    obtain ⟨n, hn⟩ := h r hr
    exists n
    intro m hm
    simp [d.distance_symm]
    exact hn m hm
  trans := by
    intro a b c h₁ h₂
    intro r hr
    obtain ⟨r₀, hr₁, hr₂⟩ := hd r hr
    obtain ⟨n₁, hn₁⟩ := h₁ r₀ hr₁
    obtain ⟨n₂, hn₂⟩ := h₂ r₀ hr₁
    exists max n₁ n₂
    intro m hm
    simp_all
    apply le_lt_trans
    sorry
    sorry
    sorry
    -- something broke
    -- apply d.distance_triangle _ (b m)
    -- apply lt_le_trans
    -- apply le_add
    -- exact hn₁ m (Nat.max_le.mp hm).left
    -- exact hn₂ m (Nat.max_le.mp hm).right
    -- exact hr₂
}

def CauchyRelation.quotient (hd: DistanceComplete D) (d₀: Endometric D) (hd₀: d₀.obedient) (d: Metric X D): Type u :=
  Quotient ⟨CauchyRelation d₀ d, CauchyRelation.equiv hd d₀ hd₀ d⟩
