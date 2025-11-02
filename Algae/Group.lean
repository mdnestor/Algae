import Algae.Monoid

variable {α: Type u}

class Group (α: Type u) extends Monoid α where
  inv: α → α
  inverse: Inverse op inv unit

export Group (inv)

local instance [Monoid α]: Add α := ⟨op⟩
local instance [Monoid α]: Zero α := ⟨unit⟩
local instance [Group α]: Neg α := ⟨inv⟩

def invop [Group α] (a b: α): α :=
  a + -b

local instance [Group α]: Sub α := ⟨λ a b ↦ a + -b⟩


theorem invop_eq [Group α] (a b: α): a - b = a + -b := by
  rfl

-- Unpacking group axioms for both notations

theorem op_inv_left [Group α] (a: α): -a + a = 0 := by
  exact Group.inverse.left a

theorem op_inv_right [Group α] (a: α): a + -a = 0 := by
  exact Group.inverse.right a

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

theorem inv_unit [Group G]: -(0: G) = 0 := by
  apply op_unit_inverses
  apply op_unit_left

theorem inv_inv [Group G] (a: G): -(-a) = a := by
  apply op_unit_inverses
  apply op_inv_left

theorem invop_self [Group α] (a: α): a - a = 0 := by
  apply op_inv_right

theorem inv_invop [Group α] (a: α): -(a - b) = b - a := by
  apply op_unit_inverses
  simp [invop_eq]
  rw [op_assoc, ←op_assoc (-b)]
  rw [op_inv_left, op_unit_left, op_inv_right]

-- In a group we can define integer multiplication via
-- 0 * a = 0, 1 * a = a, 2 * a = a + a, ... and -1 * a = 1 * -a, -2 * a = 2 * (-a), ...

theorem nmul_neg_left [Group α] (a: α) (n: Nat): n • (-a) + n • a = 0 := by
  apply nmul_inverses n
  exact op_inv_left a

theorem nmul_neg_right [Group α] (a: α) (n: Nat): n • a + n • -a = 0 := by
  apply nmul_inverses n
  exact op_inv_right a

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
  | zero => simp [nmul_zero, op_unit_left]
  | succ p hp =>
    rw [Nat.add_comm, ←nmul_add, nmul_one]
    rw [Nat.add_comm, ←nmul_add, nmul_one]
    rw [op_assoc, ←op_assoc (p • a)]
    rw [hp, op_unit_left, op_inv_right]

theorem zmul_neg' [Group α] (a: α) (n: Int): -(n • a) = n • -a := by
  apply op_unit_inverses
  induction n <;> apply nmul_inv

theorem zmul_add [Group α] (a: α) (m n: Int): m • a + n • a = (m + n) • a := by
  induction m with
  | ofNat p => induction p with
    | zero => simp [zmul_zero, op_unit_left]
    | succ p hp => sorry
  | negSucc p => sorry

theorem zmul_neg [Group α] (a: α) (n: Int): n • (-a) = -n • a := by
  induction n with
  | ofNat p => calc
    Int.ofNat p • -a
    _ = p • -a := by rfl
    _ = -Int.ofNat p • a := sorry
  | negSucc p => sorry


theorem op_cancel_left [Group G] {a b c: G} (h: a + b = a + c): b = c := by
  calc b
    _ = 0 + b        := by rw [op_unit_left]
    _ = -a + a + b   := by rw [op_inv_left]
    _ = -a + (a + b) := by rw [op_assoc]
    _ = -a + (a + c) := by rw [h]
    _ = -a + a + c   := by rw [op_assoc]
    _ = 0 + c        := by rw [op_inv_left]
    _ = c            := by rw [op_unit_left]


theorem op_cancel_right [Group G] {a b c: G} (h: a + c = b + c): a = b := by
  have group: Group G := by assumption
  apply Eq.symm
  have := @op_cancel_left _ group.opposite c b a
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
theorem inv_op [Group G] (a b: G): -(a + b) = -b + -a := by
  apply op_unit_inverses
  sorry

-- Fix a ∈ G. Then the map G → G defined by b ↦ a * b is a bijection (permutation) on G.
theorem Group.self_bijective [Group G] (a: G): Function.Bijective (λ b ↦ a + b) := by
  sorry



class GroupHom [Group α] [Group β] (f: α → β): Prop extends MonoidHom f where
  inv_preserving: ∀ a, f (-a) = -(f a)



class Subgroup [Group α] (S: Set α) extends Submonoid S where
  inv_closed: ∀ a, a ∈ S → inv a ∈ S

theorem kernel_subgroup [Group α] [Group β] {f: α → β} (hf: GroupHom f): Subgroup (Kernel f) := {
  unit_mem := (Kernel.submonoid hf.toMonoidHom).unit_mem
  op_closed := (Kernel.submonoid hf.toMonoidHom).op_closed
  inv_closed := by
    intro x hx
    calc
      f (-x)
      _ = -(f x) := by rw [hf.inv_preserving]
      _ = -unit := by rw [hx]
      _ = -0 := by rfl
      _ = 0 := by rw [inv_unit]
}
