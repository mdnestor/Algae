import Algae.Monoid

variable {G: Type u}

-- TODO: same for unital magma, we might want 2 fields for left/right inverse...
class Group (G: Type u) extends Monoid G, Neg G where
  add_inverse: Inverse add neg 0

-- In an additive group we can use the notation a - b to mean a + (-b)
instance [Group G]: Sub G := {
  sub := λ a b ↦ a + -b
}

theorem add_negative_left [Group G] (a: G): -a + a = 0 := by
  exact Group.add_inverse.left a

theorem add_negative_right [Group G] (a: G): a + -a = 0 := by
  exact Group.add_inverse.right a

-- In a group we can define integer multiplication via
-- 0 * a = 0, 1 * a = a, 2 * a = a + a, ... and -1 * a = 1 * -a, -2 * a = 2 * (-a), ...
def Group.smul [Group G] (k: Int) (a: G): G :=
  match k with
  | Int.ofNat n => n • a
  | Int.negSucc n => n • -a

instance [Group G]: SMul Int G := {
  smul := Group.smul
}

theorem add_cancel_left [Group G] {a b c: G} (h: a + b = a + c): b = c := by
  calc b
    _ = 0 + b        := by rw [add_zero_left]
    _ = -a + a + b   := by rw [add_negative_left]
    _ = -a + (a + b) := by rw [add_associative]
    _ = -a + (a + c) := by rw [h]
    _ = -a + a + c   := by rw [add_associative]
    _ = 0 + c        := by rw [add_negative_left]
    _ = c            := by rw [add_zero_left]

theorem add_cancel_right [Group G] {a b c: G} (h: a + c = b + c): a = b := by
  sorry

-- todo: show the set of permutations on a set form a group


class CommutativeGroup (G: Type u) extends Group G, CommutativeMagma G

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
theorem negative_negative [Group G] (a: G): -(-a) = a := by
  sorry

-- "socks shoes" property
theorem negative_add [Group G] (a b: G): -(a + b) = -b + -a := by
  sorry

-- Fix a ∈ G. Then the map G → G defined by b ↦ a * b is a bijection (permutation) on G.
theorem Group.self_bijective [Group G] (a: G): Function.Bijective (λ b ↦ a + b) := by
  sorry




-- TODO: same for unital magma, we might want 2 fields for left/right inverse...
class MulGroup (G: Type u) extends MulMonoid G, Inv G where
  mul_inverse: Inverse mul inv 1

-- In a multiplicative group we can use the notation a / b to mean a * b⁻¹
instance [MulGroup G]: Div G := {
  div := λ a b ↦ a * b⁻¹
}

theorem mul_inverse_left [MulGroup G] (a: G): a⁻¹ * a = 1 := by
  exact MulGroup.mul_inverse.left a

theorem mul_inverse_right [MulGroup G] (a: G): a * a⁻¹ = 1 := by
  exact MulGroup.mul_inverse.right a

-- In a multiplicative group we can define integer powers.
def MulGroup.npow [MulGroup G] (a: G) (k: Int): G :=
  match k with
  | Int.ofNat n => a ^ n
  | Int.negSucc n => (a⁻¹) ^ n

instance [MulGroup G]: HPow G Int G := {
  hPow := MulGroup.npow
}

-- blabla clone some theorems

class CommutativeMulGroup (G: Type u) extends MulGroup G, CommutativeMulMagma G
