/-

Define the extended natural numbers with infinity.

-/

import Algae.SetTheory.Operation
import Algae.SetTheory.Relation
import Algae.SetTheory.Subset

def ENat: Type :=
  Nat ⊕ Unit

abbrev 𝔼: Type :=
  ENat

instance: Coe Nat 𝔼 := {
  coe := λ n ↦ Sum.inl n
}

instance {n: Nat}: OfNat 𝔼 (n: Nat) := {
  ofNat := n
}

namespace ENat

def infty: 𝔼 :=
  Sum.inr Unit.unit

instance: DecidableEq 𝔼 :=
  instDecidableEqSum

def add: Op 𝔼 :=
  λ a b ↦ match a with
    | Sum.inl a => match b with
      | Sum.inl b => a + b
      | Sum.inr _ => infty
    | Sum.inr _ => infty

instance: Add 𝔼 := {
  add := add
}

def mul: Op 𝔼 :=
  λ a b ↦ match a with
    | Sum.inl a => match b with
      | Sum.inl b => a * b
      | Sum.inr _ => if a = 0 then 0 else infty
    | Sum.inr _ => if b = 0 then 0 else infty

instance: Mul 𝔼 := {
  mul := mul
}

def le: Endorelation 𝔼 :=
  λ a b ↦ match b with
    | Sum.inl b => match a with
      | Sum.inl a => a ≤ b
      | Sum.inr _ => False
    | Sum.inr _ => True

instance: LE 𝔼 := {
  le := le
}

instance LE.toLT {α: Type u} [LE α]: LT α := {
  lt := λ a b ↦ a ≤ b ∧ a ≠ b
}

def lt: Endorelation 𝔼 :=
  LE.toLT.lt

instance: LT 𝔼 :=
  LE.toLT

/-

First the additive structure of 𝔼:
- it is a commutative monoid with 0 the identity, i.e.
  - associative
  - identity left and right
  - commutative
- it is also cancellative
- infty is an absorbing element

-/

theorem add_assoc (a b c: 𝔼): (a + b) + c = a + (b + c) := by
  match a with
  | Sum.inl a => match b with
    | Sum.inl b => match c with
      | Sum.inl c => sorry
      | Sum.inr c => rfl
    | Sum.inr b => rfl
  | Sum.inr a => rfl

theorem add_zero_left (a: 𝔼): 0 + a = a := by
  sorry

theorem add_zero_right (a: 𝔼): a + 0 = a := by
  sorry

theorem add_comm (a b: 𝔼): a + b = b + a := by
  sorry

theorem lt_infty_iff_neq_infty (a: 𝔼): a < infty ↔ a ≠ infty := by
  constructor
  intro h
  sorry
  intro h
  sorry

theorem add_cancel_left {a b c: 𝔼} (h: a + b = a + c) (ha: a ≠ infty): b = c := by
  sorry

theorem add_cancel_right {a b c: 𝔼} (h: a + c = b + c) (hc: c ≠ infty): a = b := by
  sorry

theorem add_infty_left (a: 𝔼): infty + a = infty := by
  sorry

theorem add_infty_right (a: 𝔼): a + infty = infty := by
  sorry

/-

Next the multiplcicative structure:
- it is a commutative monoid with identity 1,
- cancellative
- infty is an absorbing element for all nonzero

-/

theorem mul_assoc (a b c: 𝔼): (a * b) * c = a * (b * c) := by
  sorry

theorem mul_one_left (a: 𝔼): 1 * a = a := by
  sorry

theorem mul_one_right (a: 𝔼): a * 1 = a := by
  sorry

theorem mul_comm (a b: 𝔼): a * b = b * a := by
  sorry

theorem mul_cancel_left {a b c: 𝔼} (h: a * b = a * c) (ha₁: a ≠ 0) (ha₂: a ≠ infty): b = c := by
  sorry

theorem mul_cancel_right {a b c: 𝔼} (h: a * c = b * c) (hc₁: c ≠ 0) (hc₂: c ≠ infty): a = b := by
  sorry


theorem mul_infty_left {a: 𝔼} (ha: a ≠ 0): infty * a = infty := by
  sorry

theorem mul_infty_right {a: 𝔼} (ha: a ≠ 0): a * infty = infty := by
  sorry

-- Interaction of additive and multiplicative structure

theorem mul_zero_left (a: 𝔼): 0 * a = 0 := by
  sorry

theorem mul_zero_right (a: 𝔼): a * 0 = 0 := by
  sorry

theorem distrib_left (a b c: 𝔼): a * (b + c) = a * b + a * c := by
  sorry

theorem distrib_right (a b c: 𝔼): (a + b) * c = a * c + b * c := by
  sorry

/-

Finally the order structure:
- Reflexive
- Transitive
- Antisymmetric
- Total

-/

theorem le_refl {a: 𝔼}: a ≤ a := by
  sorry

theorem le_trans {a b c: 𝔼} (h₁: a ≤ b) (h₂: b ≤ c): a ≤ c := by
  sorry

theorem le_antisymm {a b: 𝔼} (h₁: a ≤ b) (h₂: b ≤ a): a = b := by
  sorry

theorem le_total {a b: 𝔼}: a ≤ b ∨ b ≤ a := by
  sorry

-- Interaction of arithmetic and order structure
theorem add_le (a b: 𝔼): a ≤ a + b := by
  sorry

theorem mul_le (a: 𝔼) {b: 𝔼} (hb: b ≠ 0): a ≤ a * b := by
  sorry

theorem lt_wfRel: WellFounded lt := by
  sorry

def max (a b: 𝔼): 𝔼 :=
  sorry

def min (a b: 𝔼): 𝔼 :=
  sorry

def sup (S: Set 𝔼): 𝔼 :=
  sorry

def inf (S: Set 𝔼): 𝔼 :=
  sorry

theorem inf_le (S: Set 𝔼) (a: 𝔼) (ha: a ∈ S): inf S ≤ a := by
  sorry

theorem inf_empty: inf ∅ = infty := by
  sorry

theorem le_sup (S: Set 𝔼) (a: 𝔼) (ha: a ∈ S): a ≤ sup S := by
  sorry

theorem sup_empty: sup ∅ = 0 := by
  sorry
