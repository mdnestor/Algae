import Algae.Monoid

variable {G: Type u}


class Group (α: Type u) extends Monoid α where
  inv: α → α
  inverse: Inverse op inv unit

export Group (inv)



instance [Group α]: Neg α := {
  neg := inv
}

instance [Group α]: Inv α := {
  inv := inv
}

theorem neg_eq [Group α] (a: α): -a = inv a := by
  rfl

theorem inv_eq [Group α] (a: α): a⁻¹ = inv a := by
  apply neg_eq

theorem add_neg_left [Group α] (a: α): -a + a = 0 := by
  exact Group.inverse.left a

theorem add_neg_right [Group α] (a: α): a + -a = 0 := by
  exact Group.inverse.right a

theorem mul_inv_left [Group α] (a: α): a⁻¹ * a = 1 := by
  apply add_neg_left

theorem mul_inv_right [Group α] (a: α): a * a⁻¹ = 1 := by
  apply add_neg_right



class CommGroup (α: Type u) extends Group α, CommMonoid α

-- In an additive group we can use the notation a - b to mean a + (-b)
instance [Group G]: Sub G := {
  sub := λ a b ↦ a + -b
}

-- theorem add_neg_left [Group G] (a: G): -a + a = 0 := by
--   exact Group.add_neg.left a

-- theorem add_neg_right [Group G] (a: G): a + -a = 0 := by
--   exact Group.add_neg.right a


theorem inv_unit [Group G]: inv (unit: G) = unit := by
  have h1: inverses (unit: G) (unit: G) := by
    constructor
    repeat exact add_zero_left 0
  have h2: inverses (unit: G) (inv unit: G) := by
    constructor
    exact add_neg_right 0
    exact add_neg_left 0
  exact inverses_unique h2 h1

theorem neg_zero [Group G]: -(0: G) = 0 := by
  apply inv_unit

theorem inv_one [Group G]: (1: G)⁻¹ = 1 := by
  apply inv_unit

-- In a group we can define integer multiplication via
-- 0 * a = 0, 1 * a = a, 2 * a = a + a, ... and -1 * a = 1 * -a, -2 * a = 2 * (-a), ...

def zmul [Group G] (k: Int) (a: G): G :=
  match k with
  | Int.ofNat n => n • a
  | Int.negSucc n => n • -a

instance [Group G]: SMul Int G := {
  smul := zmul
}

theorem zmul_add [Group α] (a: α) (m n: Int): m • a + n • a = (m + n) • a := by
  induction m with
  | ofNat p => sorry
  | negSucc p => sorry

theorem zmul_neg [Group α] (a: α) (n: Int): n • (-a) = -n • a := by
  induction n with
  | ofNat p => sorry
  | negSucc p => sorry

theorem zmul_neg' [Group α] (a: α) (n: Int): n • (-a) = -(n • a) := by
  sorry

theorem op_cancel_left [Group G] {a b c: G} (h: op a b = op a c): b = c := by
  calc b
    _ = 0 + b        := by rw [add_zero_left]
    _ = -a + a + b   := by rw [add_neg_left]
    _ = -a + (a + b) := by rw [add_assoc]
    _ = -a + (a + c) := by (repeat rw [add_eq]); rw [h]
    _ = -a + a + c   := by rw [add_assoc]
    _ = 0 + c        := by rw [add_neg_left]
    _ = c            := by rw [add_zero_left]

theorem add_cancel_left [Group G] {a b c: G} (h: a + b = a + c): b = c := by
  apply op_cancel_left h

theorem mul_cancel_left [Group G] {a b c: G} (h: a * b = a * c): b = c := by
  apply op_cancel_left h

theorem add_cancel_right [Group G] {a b c: G} (h: a + c = b + c): a = b := by
  sorry

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
theorem neg_neg [Group G] (a: G): -(-a) = a := by
  sorry

-- "socks shoes" property
theorem neg_add [Group G] (a b: G): -(a + b) = -b + -a := by
  sorry

-- Fix a ∈ G. Then the map G → G defined by b ↦ a * b is a bijection (permutation) on G.
theorem Group.self_bijective [Group G] (a: G): Function.Bijective (λ b ↦ a + b) := by
  sorry
