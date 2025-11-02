import Algae.Monoid

variable {α: Type u}


class Group (α: Type u) extends Monoid α where
  inv: α → α
  inverse: Inverse op inv unit

export Group (inv)

-- Additive notation for a group
instance [Group α]: Neg α := {
  neg := inv
}

instance [Group α]: Sub α := {
  sub := λ a b ↦ a + -b
}

theorem neg_eq [Group α] (a: α): -a = inv a := by
  rfl

theorem sub_eq [Group α] (a b: α): a - b = op a (inv b) := by
  rfl

-- Multiplicative notation for a group
instance [Group α]: Inv α := {
  inv := inv
}

instance [Group α]: Div α := {
  div := λ a b ↦ a * b⁻¹
}

theorem inv_eq [Group α] (a: α): a⁻¹ = inv a := by
  apply neg_eq

theorem div_eq [Group α] (a b: α): a / b = op a (inv b) := by
  apply sub_eq

-- Unpacking group axioms for both notations

theorem op_inv_left [Group α] (a: α): op (inv a) a = unit := by
  exact Group.inverse.left a

theorem op_inv_right [Group α] (a: α): op a (inv a) = unit := by
  exact Group.inverse.right a

theorem add_neg_left [Group α] (a: α): -a + a = 0 := by
  apply op_inv_left

theorem add_neg_right [Group α] (a: α): a + -a = 0 := by
  apply op_inv_right

theorem mul_inv_left [Group α] (a: α): a⁻¹ * a = 1 := by
  apply op_inv_left

theorem mul_inv_right [Group α] (a: α): a * a⁻¹ = 1 := by
  apply op_inv_right

-- Opposite group
-- TODO: is there a way to employ this usefully..? avoid repeating arguments?
def Group.opposite [Group α]: Group α := {
  op := Group.toMonoid.opposite.op
  identity := Group.toMonoid.opposite.identity
  assoc := Group.toMonoid.opposite.assoc
  inv := inv
  inverse := ⟨inverse.right, inverse.left⟩
}


class CommGroup (α: Type u) extends Group α, CommMonoid α

theorem inverses_inv [Group α] (a: α): inverses a (-a) := by
  constructor
  exact op_inv_right a
  exact op_inv_left a

theorem op_unit_inverses [Group α] {a b: α} (h: a + b = 0): -a = b := by
  apply left_right_inverse_eq
  exact op_inv_left a
  exact h

theorem inv_unit [Group G]: inv (unit: G) = unit := by
  apply op_unit_inverses
  apply op_unit_left

theorem neg_zero [Group G]: -(0: G) = 0 := by
  apply inv_unit

theorem inv_one [Group G]: (1: G)⁻¹ = 1 := by
  apply inv_unit

theorem inv_inv [Group G] (a: G): inv (inv a) = a := by
  apply op_unit_inverses
  apply add_neg_left

theorem neg_neg [Group G] (a: G): -(-a) = a := by
  apply inv_inv

theorem negop_self [Group α] (a: α): a - a = 0 := by
  apply op_inv_right

theorem neg_sub [Group α] (a: α): -(a - b) = b - a := by
  apply op_unit_inverses
  simp [sub_eq, add_eq, zero_eq]
  rw [Monoid.assoc, ←Monoid.assoc (inv b)]
  rw [op_inv_left, op_unit_left, op_inv_right]

-- In a group we can define integer multiplication via
-- 0 * a = 0, 1 * a = a, 2 * a = a + a, ... and -1 * a = 1 * -a, -2 * a = 2 * (-a), ...

theorem nmul_neg_left [Group α] (a: α) (n: Nat): n • (-a) + n • a = 0 := by
  apply nmul_inverses n
  exact add_neg_left a

theorem nmul_neg_right [Group α] (a: α) (n: Nat): n • a + n • -a = 0 := by
  apply nmul_inverses n
  exact add_neg_right a

def zmul [Group α] (k: Int) (a: α): α :=
  match k with
  | Int.ofNat n => n • a
  | Int.negSucc n => n.succ • -a

instance [Group G]: SMul Int G := {
  smul := zmul
}


theorem zmul_zero [Group α] (a: α): (0: Int) • a = (0: α) := by
  rfl

theorem nmul_inv [Group α] (a: α) (n: Nat): (n • a) + (n • -a) = 0 := by
  induction n with
  | zero => simp [nmul_zero, add_zero_left]
  | succ p hp =>
    rw [Nat.add_comm, ←nmul_add, nmul_one]
    rw [Nat.add_comm, ←nmul_add, nmul_one]
    rw [add_assoc, ←add_assoc (p • a)]
    rw [hp, add_zero_left, add_neg_right]

theorem zmul_neg' [Group α] (a: α) (n: Int): -(n • a) = n • -a := by
  apply op_unit_inverses
  induction n <;> apply nmul_inv

theorem zmul_add [Group α] (a: α) (m n: Int): m • a + n • a = (m + n) • a := by
  induction m with
  | ofNat p => induction p with
    | zero => simp [zmul_zero, add_zero_left]
    | succ p hp => sorry
  | negSucc p => sorry

theorem zmul_neg [Group α] (a: α) (n: Int): n • (-a) = -n • a := by
  induction n with
  | ofNat p => calc
    Int.ofNat p • -a
    _ = p • -a := by rfl
    _ = -Int.ofNat p • a := sorry
  | negSucc p => sorry


theorem op_cancel_left [Group G] {a b c: G} (h: op a b = op a c): b = c := by
  calc b
    _ = 0 + b        := by rw [add_zero_left]
    _ = -a + a + b   := by rw [add_neg_left]
    _ = -a + (a + b) := by rw [add_assoc]
    _ = -a + (a + c) := by to_generic; rw [h]
    _ = -a + a + c   := by rw [add_assoc]
    _ = 0 + c        := by rw [add_neg_left]
    _ = c            := by rw [add_zero_left]

theorem add_cancel_left [Group G] {a b c: G} (h: a + b = a + c): b = c := by
  apply op_cancel_left h

theorem mul_cancel_left [Group G] {a b c: G} (h: a * b = a * c): b = c := by
  apply op_cancel_left h

theorem add_cancel_right [Group G] {a b c: G} (h: a + c = b + c): a = b := by
  have group: Group G := by assumption
  apply Eq.symm
  have := @add_cancel_left _ group.opposite c b a
  apply this
  apply Eq.symm

  repeat rw [@add_eq]
  repeat rw [@add_eq] at h
  rw [Group.opposite]
  sorry
  -- exact h


  -- repeat rw [add_eq] at h


  -- sorry

-- Sanity check to make sure everything works.
theorem square_self_zero [Group G] {a: G} (h: 2 • a = a): a = 0 := by
  /-
  Idea:
  a = 0 + a
    = (-a + a) + a
    = -a + (a + a)
    = -a + (2 • a)
    = -a + a -- by assupmtion
    = 0
  -/
  sorry

-- TODO theorem: if a*b = e then a = b⁻¹.


-- alternatively could show the map a ↦ a⁻¹ is an involution?


-- "socks shoes" property
theorem neg_add [Group G] (a b: G): -(a + b) = -b + -a := by
  apply op_unit_inverses
  sorry

-- Fix a ∈ G. Then the map G → G defined by b ↦ a * b is a bijection (permutation) on G.
theorem Group.self_bijective [Group G] (a: G): Function.Bijective (λ b ↦ a + b) := by
  sorry



class GroupHom [Group α] [Group β] (f: α → β): Prop extends MonoidHom f where
  inv_preserving: ∀ a, f (inv a) = inv (f a)



class Subgroup [Group α] (S: Set α) extends Submonoid S where
  inv_closed: ∀ a, a ∈ S → inv a ∈ S

theorem kernel_subgroup [Group α] [Group β] {f: α → β} (hf: GroupHom f): Subgroup (Kernel f) := {
  unit_mem := (Kernel.submonoid hf.toMonoidHom).unit_mem
  op_closed := (Kernel.submonoid hf.toMonoidHom).op_closed
  inv_closed := by
    intro x hx
    calc
      f (inv x)
      _ = inv (f x) := by rw [hf.inv_preserving]
      _ = inv unit := by rw [hx]
      _ = unit := by rw [inv_unit]
}
