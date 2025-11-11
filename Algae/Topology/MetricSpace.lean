
import Algae.GroupTheory.Monoid

variable {X: Type u} {D: Type v}

open Monoid

/-

A (generalized) metric space consists of

- a set X
- a set D equipped with ordering ≤, bottom ⊥, addition +.
- a function d: X × X → D
- d(x, y) = ⊥ ↔ x = y
- d(x, y) = d(y, x)
- Triangle inequality: d(x, z) ≤ d(x, y) + d(x, z)

-/

-- An "order bottom" structure. TODO move elsewhere

instance [LE D]: LT D := {
  lt := λ x y ↦ x ≤ y ∧ ¬ y ≤ x
}

class OrderBottom (X: Type u) where
  le: X → X → Prop
  bottom: X
  bottom_le: ∀ x, le bottom x

instance [OrderBottom D]: LE D := {
  le := OrderBottom.le
}

notation "⊥" => OrderBottom.bottom

-- A "distance space" structure

class DistanceSpace (D: Type v) where
  le: D → D → Prop
  bottom: D
  add: D → D → D
  bottom_le: ∀ x, le bottom x

instance [DistanceSpace D]: Magma D := {
  op := DistanceSpace.add
}

instance [DistanceSpace D]: OrderBottom D := {
  le := DistanceSpace.le
  bottom := DistanceSpace.bottom
  bottom_le := DistanceSpace.bottom_le
}

-- Metric space

class Metric (X: Type u) (D: Type v) [DistanceSpace D] where
  distance: X → X → D
  distance_bot_iff: ∀ x y, distance x y = ⊥ ↔ x = y
  distance_symm: ∀ x y, distance x y = distance y x
  distance_triangle: ∀ x y z, distance x z ≤ distance x y + distance y z

instance [DistanceSpace D] [Metric X D]: CoeFun (Metric X D) (λ _ ↦ X → X → D) := {
  coe _ := Metric.distance
}

-- From now on assume D has a distance space structure.

variable [DistanceSpace D]

-- Unpack metric axioms

theorem distance_bot_iff [d: Metric X D]: ∀ x y, d x y = ⊥ ↔ x = y := by
  exact Metric.distance_bot_iff

theorem distance_symm [d: Metric X D]: ∀ x y, d x y = d y x := by
  exact Metric.distance_symm

theorem distance_triangle [d: Metric X D]: ∀ x y z, d x z ≤ d x y + d y z := by
  exact Metric.distance_triangle

-- First theorem of substabce: distance from any point to itself is the bottom element.

theorem dist_self_bot [d: Metric X D] (x: X): d x x = ⊥ := by
  apply (distance_bot_iff x x).mpr
  rfl

def converges_to (d: Metric X D) (s: Nat → X) (x: X): Prop :=
  ∀ r, ⊥ < r → ∃ n, ∀ m, n ≤ m → d (s m) x < r

def convergent (d: Metric X D) (s: Nat → X): Prop :=
  ∃ x, converges_to d s x

-- optional: define the limit of a convergent sequence via choose

theorem constant_sequence_converges (d: Metric X D) (x: X): converges_to d (λ _ ↦ x) x := by
  intro _ hr
  exists 123
  intro _ _
  rw [dist_self_bot]
  exact hr

def tail (s: Nat → X) (t: Nat): Nat → X :=
  λ n ↦ s (n + t)

theorem converges_iff_tails_converge (d: Metric X D) (s: Nat → X) (x: X): converges_to d s x ↔ ∀ t, converges_to d (tail s t) x := by
  constructor
  · intro h t r hr
    obtain ⟨n, hn⟩ := h r hr
    exists n - t
    intro m hm
    apply hn (m + t)
    exact Nat.le_add_of_sub_le hm
  · intro h
    exact h 0

theorem limit_unique {d: Metric X D} {s: Nat → X} {x₁ x₂: X} (h₁: converges_to d s x₁) (h₂: converges_to d s x₂): x₁ = x₂ := by
  sorry

/-

TODO:

- define open/closed ball and sphere
- define an open set
- monotone ball inclusion
- boundedness? maybe
-/
