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
  rfl

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

--theorem neg_unique [Group G] -- oh um i don't know how the inhertiance you do it
-- wdym ?
-- i mean neg is just inverse
-- this is just inverse unique ?
-- why did you bring it up then what
-- 0 + 0 = 0
-- 0 + -0 = 0

-- do we even need unique like
-- can't we just um
-- a + 0 = b => a = b ?
-- oh ok equivalent?

theorem neg_zero [Group G]: (0: G) = -(0: G) := by
  have h1: Monoid.inverses (0: G) (0: G) := by
    constructor
    repeat exact add_zero_left 0
  have h2: Monoid.inverses (0: G) (-0: G) := by
    constructor
    exact add_neg_right 0
    exact add_neg_left 0
  exact inverses_unique h1 h2

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
    _ = -a + a + b   := by rw [add_neg_left]
    _ = -a + (a + b) := by rw [add_assoc]
    _ = -a + (a + c) := by rw [h]
    _ = -a + a + c   := by rw [add_assoc]
    _ = 0 + c        := by rw [add_neg_left]
    _ = c            := by rw [add_zero_left]

theorem add_cancel_right [Group G] {a b c: G} (h: a + c = b + c): a = b := by
  sorry

def Permutation (α: Type u): Set (α → α) :=
  λ f ↦ Function.invertible f


-- noncomputable instance PermutationGroup (α: Type u): Group (Permutation α) := {
--   add := λ f g ↦ ⟨g.val ∘ f.val, Function.invertible_comp f.property g.property⟩
--   zero := ⟨id, Function.invertible_id⟩
--   add_zero := by constructor <;> (intro; rfl)
--   add_assoc := by intro _ _ _; rfl
--   neg := λ f ↦ ⟨f.property.choose, ⟨f, f.property.choose_spec.2, f.property.choose_spec.1⟩⟩
--   add_neg := by
--     constructor <;> (intro ⟨f, hf⟩; simp; congr)
--     exact hf.choose_spec.right
--     exact hf.choose_spec.left
-- }

--class CommGroup (G: Type u) extends Group G, CommMonoid G

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
