import Algae.Monoid

variable {α: Type u} {β: Type v} {γ: Type w}

/-
  Group
-/

class Group (α: Type u) extends Monoid α, Neg α where
  add_inverse: Inverse add neg 0

-- In an additive group, we can use the notation a - b to mean a + (-b).
instance [Group α]: Sub α := {
  sub := λ a b ↦ a + -b
}

-- -a + a = a + -a = 0.
theorem add_negative_left [Group α] (a: α): -a + a = 0 := by
  exact Group.add_inverse.left a

theorem add_negative_right [Group α] (a: α): a + -a = 0 := by
  exact Group.add_inverse.right a

-- a + b = a + c => b = c.
theorem add_cancel_left [Group α] {a b c: α} (h: a + b = a + c): b = c := by
  calc b
    _ = 0 + b        := by rw [add_zero_left]
    _ = -a + a + b   := by rw [add_negative_left]
    _ = -a + (a + b) := by rw [add_associative]
    _ = -a + (a + c) := by rw [h]
    _ = -a + a + c   := by rw [add_associative]
    _ = 0 + c        := by rw [add_negative_left]
    _ = c            := by rw [add_zero_left]

-- a + c = b + c => a = b.
theorem add_cancel_right [Group α] {a b c: α} (h: a + c = b + c): a = b := by
  calc a
    _ = a + 0        := by rw [add_zero_right]
    _ = a + (c + -c) := by rw [add_negative_right]
    _ = a + c + -c   := by rw [add_associative]
    _ = b + c + -c   := by rw [h]
    _ = b + (c + -c) := by rw [add_associative]
    _ = b + 0        := by rw [add_negative_right]
    _ = b            := by rw [add_zero_right]

-- 0 = -0.
theorem neg_zero [Group α]: (0: α) = -(0: α) := by
  have h1: UnitalMagma.inverses (0: α) (0: α) := by
    constructor
    repeat exact add_zero_left 0
  have h2: UnitalMagma.inverses (0: α) (-0: α) := by
    constructor
    exact add_negative_right 0
    exact add_negative_left 0
  exact inverses_unique h1 h2

-- If a + b = 0, then a = -b.
theorem add_eq_zero [Group α] (a b: α) (h: a + b = 0): a = -b := by
  apply add_cancel_right (c := b)
  rw [add_negative_left]
  exact h

-- The map a ↦ -a is an involution.
theorem negative_negative [Group α] (a: α): -(-a) = a := by
  apply add_cancel_right (c := -a)
  rw [add_negative_left, add_negative_right]

-- "socks shoes" property
theorem negative_add [Group α] (a b: α): -(a + b) = -b + -a := by
  apply add_cancel_right (c := (a + b))
  rw [add_negative_left]
  apply Eq.symm -- ugh
  calc
    -b + -a + (a + b)
    _ = -b + (-a + (a + b)) := by rw [add_associative]
    _ = -b + ((-a + a) + b) := by rw [add_associative]
    _ = -b + (0 + b)        := by rw [add_negative_left]
    _ = -b + b              := by rw [add_zero_left]
    _ = 0                   := by rw [add_negative_left]

-- In a group, we can define integer multiplication as:
-- 0 * a = 0, 1 * a = a, 2 * a = a + a, ..., and
-- -1 * a = 1 * -a, -2 * a = 2 * (-a), ...
def Group.smul [Group α] (k: Int) (a: α): α :=
  match k with
  | Int.ofNat n => n • a
  | Int.negSucc n => n • -a

instance [Group α]: SMul Int α := {
  smul := Group.smul
}

-- If 2 • a = a, then a = 0.
theorem square_self_zero [Group α] {a: α} (h: 2 • a = a): a = 0 := by
  calc
    a
    _ = 0 + a        := by rw [add_zero_left]
    _ = (-a + a) + a := by rw [add_negative_left]
    _ = -a + (a + a) := by rw [add_associative]
    _ = -a + (2 • a) := by rw [UnitalMagma.npow_two a]
    _ = -a + a       := by rw [h]
    _ = 0            := by rw [add_negative_left]



/-
  Group homomorphism
-/

class GroupHom [Group α] [Group β] (f: α → β): Prop extends UnitalMagmaHom f where
  neg_preserving: ∀ a, f (-a) = -(f a)

-- TODO: simplify these using unital magma hom extension
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



/-
  Subgroup
-/

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



/-
  Commutative group
-/

class CommutativeGroup (G: Type u) extends Group G, CommutativeMagma G
