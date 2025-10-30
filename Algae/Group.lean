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
  have h1: UnitalMagma.inverses (0: G) (0: G) := by
    constructor
    repeat exact add_zero_left 0
  have h2: UnitalMagma.inverses (0: G) (-0: G) := by
    constructor
    exact add_negative_right 0
    exact add_negative_left 0
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
    _ = -a + a + b   := by rw [add_negative_left]
    _ = -a + (a + b) := by rw [add_associative]
    _ = -a + (a + c) := by rw [h]
    _ = -a + a + c   := by rw [add_associative]
    _ = 0 + c        := by rw [add_negative_left]
    _ = c            := by rw [add_zero_left]

theorem add_cancel_right [Group G] {a b c: G} (h: a + c = b + c): a = b := by
  sorry

def Permutation (α: Type u): Set (α → α) :=
  λ f ↦ Function.invertible f

noncomputable instance PermutationGroup (α: Type u): Group (Permutation α) := {
  add := λ f g ↦ ⟨g.val ∘ f.val, Function.invertible_comp f.property g.property⟩
  zero := ⟨id, Function.invertible_id⟩
  add_identity := by constructor <;> (intro; rfl)
  add_associative := by intro _ _ _; rfl
  neg := λ f ↦ ⟨f.property.choose, ⟨f, f.property.choose_spec.2, f.property.choose_spec.1⟩⟩
  add_inverse := by
    constructor <;> (intro ⟨f, hf⟩; simp; congr)
    exact hf.choose_spec.right
    exact hf.choose_spec.left
}

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







-- A group hom needs also to preserve inv
class GroupHom [Group α] [Group β] (f: α → β): Prop extends UnitalMagmaHom f where
  neg_preserving: ∀ a, f (-a) = -(f a)

-- todo: simplify these using unital magma home xtension
theorem GroupHom.id [Group α]: GroupHom (@id α) := {
  add_preserving := MagmaHom.id.add_preserving
  zero_preserving := PointedSetHom.id.zero_preserving
  neg_preserving := by intro; rfl
}

theorem GroupHom.comp [Group α] [Group β] [Group γ] {f: α → β} {g: β → γ} (hf: GroupHom f) (hg: GroupHom g): GroupHom (g ∘ f) := {
  add_preserving := (MagmaHom.comp hf.toMagmaHom hg.toMagmaHom).add_preserving
  zero_preserving := (PointedSetHom.comp hf.toPointedSetHom hg.toPointedSetHom).zero_preserving
  neg_preserving := by intro; simp [hf.neg_preserving, hg.neg_preserving]
}

def Group.element_map {α: Type u} [Group α] (a: α): (α → α) :=
  λ x ↦ x + a

theorem Group.element_map_invertible {α: Type u} [Group α] (a: α): Function.invertible (Group.element_map a) := by
  exists λ x ↦ x + -a
  constructor <;> (
    ext
    simp [
      element_map,
      add_associative,
      add_negative_left,
      add_negative_right,
      add_zero_right,
      Function.id
    ]
  )

def Group.element_permutation (α: Type u) [Group α]: α → Permutation α :=
  λ a ↦ ⟨element_map a, element_map_invertible a⟩

def Group.element_permutation_injective (α: Type u) [Group α]: Function.Injective (Group.element_permutation α) := by
  sorry

theorem GroupHom.element_permutation_hom (α: Type u) [Group α]:
  GroupHom (Group.element_permutation α) := {
    add_preserving := by
      intros
      simp [Group.element_permutation]
      congr
      ext
      simp [Group.element_map]
      rw [add_associative]
    zero_preserving := by
      intros
      simp [Group.element_permutation]
      congr
      ext
      simp [Group.element_map]
      rw [add_zero_right]
    neg_preserving := by
      sorry
      -- intro a
      -- obtain ⟨a', ha'⟩ := Group.element_map_invertible a
      -- ext x
  }

-- new theorem?

class Subgroup [Group α] (S: Set α): Prop extends SubMagma S, SubPointedSet S where
  neg_closed: ∀ a: α, a ∈ S → -a ∈ S

theorem kernel_subgroup [Group α] [Group β] (f: α → β) (hf: GroupHom f):
  Subgroup (kernel f) := {
  zero_mem := (SubPointedSet.kernel hf.toPointedSetHom).zero_mem
  add_closed := (SubUnitalMagma.kernel_sub hf.toUnitalMagmaHom).add_closed
  neg_closed := by
    intro a h
    calc
      f (-a)
      _ = -f a := by rw [hf.neg_preserving]
      _ = -0   := by rw [h]
      _ = 0    := by rw [←neg_zero]
}

-- i am going to get water brb :) its dark in the kithcen.. i am eating an apple
-- sorry continue what you were doing


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
