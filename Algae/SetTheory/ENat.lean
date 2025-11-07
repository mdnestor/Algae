/-

Define the extended natural numbers with infinity.

-/

import Algae.SetTheory.Operation
import Algae.SetTheory.Relation
import Algae.SetTheory.Subset

def ENat: Type :=
  Nat ⊕ Unit

instance: Coe Nat ENat := {
  coe := fun n => Sum.inl n
}

instance {n: Nat}: OfNat ENat (n: Nat) := {
  ofNat := n
}

def ENat.infty: ENat :=
  Sum.inr Unit.unit

instance: DecidableEq ENat :=
  instDecidableEqSum

def ENat.add: Op ENat :=
  fun a b => match a with
    | Sum.inl a => match b with
      | Sum.inl b => a + b
      | Sum.inr _ => infty
    | Sum.inr _ => infty

instance: Add ENat := {
  add := ENat.add
}

def ENat.mul: Op ENat :=
  fun a b => match a with
    | Sum.inl a => match b with
      | Sum.inl b => a * b
      | Sum.inr _ => if a = 0 then 0 else infty
    | Sum.inr _ => if b = 0 then 0 else infty

instance: Mul ENat := {
  mul := ENat.mul
}

def ENat.le: Endorelation ENat :=
  fun a b => match b with
    | Sum.inl b => match a with
      | Sum.inl a => a ≤ b
      | Sum.inr _ => False
    | Sum.inr _ => True

instance: LE ENat := {
  le := ENat.le
}

instance LE.toLT {α: Type u} [LE α]: LT α := {
  lt := fun a b => a ≤ b ∧ a ≠ b
}

def ENat.lt: Endorelation ENat :=
  LE.toLT.lt

instance: LT ENat :=
  LE.toLT

/-

First the additive structure of ENat:
- it is a commutative monoid with 0 the identity, i.e.
  - associative
  - identity left and right
  - commutative
- it is also cancellative
- infty is an absorbing element

-/

theorem ENat.add_assoc (a b c: ENat): (a + b) + c = a + (b + c) := by
  match a with
  | Sum.inl a => match b with
    | Sum.inl b => match c with
      | Sum.inl c => sorry
      | Sum.inr c => rfl
    | Sum.inr b => rfl
  | Sum.inr a => rfl

theorem ENat.add_zero_left (a: ENat): 0 + a = a := by
  sorry

theorem ENat.add_zero_right (a: ENat): a + 0 = a := by
  sorry

theorem ENat.add_comm (a b: ENat): a + b = b + a := by
  sorry

theorem ENat.lt_infty_iff_neq_infty (a: ENat): a < infty ↔ a ≠ infty := by
  constructor
  intro h
  sorry
  intro h
  sorry

theorem ENat.add_cancel_left {a b c: ENat} (h: a + b = a + c) (ha: a ≠ infty): b = c := by
  sorry

theorem ENat.add_cancel_right {a b c: ENat} (h: a + c = b + c) (hc: c ≠ infty): a = b := by
  sorry

theorem ENat.add_infty_left (a: ENat): infty + a = infty := by
  sorry

theorem ENat.add_infty_right (a: ENat): a + infty = infty := by
  sorry

/-

Next the multiplcicative structure:
- it is a commutative monoid with identity 1,
- cancellative
- infty is an absorbing element for all nonzero

-/

theorem ENat.mul_assoc (a b c: ENat): (a * b) * c = a * (b * c) := by
  sorry

theorem ENat.mul_one_left (a: ENat): 1 * a = a := by
  sorry

theorem ENat.mul_one_right (a: ENat): a * 1 = a := by
  sorry

theorem ENat.mul_comm (a b: ENat): a * b = b * a := by
  sorry

theorem ENat.mul_cancel_left {a b c: ENat} (h: a * b = a * c) (ha₁: a ≠ 0) (ha₂: a ≠ infty): b = c := by
  sorry

theorem ENat.mul_cancel_right {a b c: ENat} (h: a * c = b * c) (hc₁: c ≠ 0) (hc₂: c ≠ infty): a = b := by
  sorry


theorem ENat.mul_infty_left {a: ENat} (ha: a ≠ 0): infty * a = infty := by
  sorry

theorem ENat.mul_infty_right {a: ENat} (ha: a ≠ 0): a * infty = infty := by
  sorry

-- Interaction of additive and multiplicative structure

theorem ENat.mul_zero_left (a: ENat): 0 * a = 0 := by
  sorry

theorem ENat.mul_zero_right (a: ENat): a * 0 = 0 := by
  sorry

theorem ENat.distrib_left (a b c: ENat): a * (b + c) = a * b + a * c := by
  sorry

theorem ENat.distrib_right (a b c: ENat): (a + b) * c = a * c + b * c := by
  sorry

/-

Finally the order structure:
- Reflexive
- Transitive
- Antisymmetric
- Total

-/

theorem ENat.le_refl {a: ENat}: a ≤ a := by
  sorry

theorem ENat.le_trans {a b c: ENat} (h₁: a ≤ b) (h₂: b ≤ c): a ≤ c := by
  sorry

theorem ENat.le_antisymm {a b: ENat} (h₁: a ≤ b) (h₂: b ≤ a): a = b := by
  sorry

theorem ENat.le_total {a b: ENat}: a ≤ b ∨ b ≤ a := by
  sorry

-- Interaction of arithmetic and order structure
theorem ENat.add_le (a b: ENat): a ≤ a + b := by
  sorry

theorem ENat.mul_le (a: ENat) {b: ENat} (hb: b ≠ 0): a ≤ a * b := by
  sorry

theorem ENat.lt_wfRel: WellFounded ENat.lt := by
  sorry

def ENat.max (a b: ENat): ENat :=
  sorry

def ENat.min (a b: ENat): ENat :=
  sorry

def ENat.sup (S: Set ENat): ENat :=
  sorry

def ENat.inf (S: Set ENat): ENat :=
  sorry

theorem ENat.inf_le (S: Set ENat) (a: ENat) (ha: a ∈ S): inf S ≤ a := by
  sorry

theorem ENat.inf_empty: inf ∅ = infty := by
  sorry

theorem ENat.le_sup (S: Set ENat) (a: ENat) (ha: a ∈ S): a ≤ sup S := by
  sorry

theorem ENat.sup_empty: sup ∅ = 0 := by
  sorry
