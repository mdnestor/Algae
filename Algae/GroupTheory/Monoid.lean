import Algae.GroupTheory.Pointed
import Algae.GroupTheory.Magma

variable {α: Type u₁} {β: Type u₂}



/-

A monoid is a set with:
- a "pointed" structure, i.e. a distinguished point 0,
- a magma structure with a binary operation,
- 0 is an identity for the operation,
- the operation is associative.

-/

class Monoid (α: Type u) extends Pointed α, Magma α where
  identity: Identity op unit
  assoc: Associative op



-- Introduce `+` and `0` notation to the monoid namespace.
namespace Monoid
scoped instance [Magma α]: Add α := ⟨op⟩
scoped instance [Pointed α]: Zero α := ⟨unit⟩

def ngen [Monoid α] (n: Nat) (a: α): α :=
  match n with
  | Nat.zero => 0
  | Nat.succ p => (ngen p a) + a

instance [Monoid α]: SMul Nat α := ⟨ngen⟩

end Monoid

open Monoid



-- Unpack axioms with notation.
theorem op_unit_left [Monoid α] (a: α): 0 + a = a := by
  exact Monoid.identity.left a

theorem op_unit_right [Monoid α] (a: α): a + 0 = a := by
  exact Monoid.identity.right a

theorem op_assoc [Monoid M] (a b c: M): a + b + c = a + (b + c) := by
  exact Monoid.assoc a b c

def inverses [Monoid α] (a b: α): Prop :=
  Inverses op a b unit

def inverses_iff [Monoid M] (a b: M): inverses a b ↔ a + b = 0 ∧ b + a = 0 := by
  rfl

/-
In a monoid we can define multiplication by natural numbers via
0 • a = 0
1 • a = a
2 • a = a + a
etc.
-/


theorem ngen_zero' [Monoid α] (a: α): 0 • a = 0 := by
  rfl

theorem ngen_zero [Monoid α] (a: α): 0 • a = (0: α) := by
  rfl

theorem ngen_succ [Monoid α] (a: α) (n: Nat): (n + 1) • a = (n • a) + a := by
  rfl

theorem ngen_one [Monoid α] (a: α): 1 • a = a := by
  rw [ngen_succ, ngen_zero, op_unit_left]

theorem ngen_two [Monoid α] (a: α): 2 • a = a + a := by
  rw [ngen_succ, ngen_one]

theorem ngen_add [Monoid α] (a: α) (m n: Nat): m • a + n • a = (m + n) • a := by
  induction n with
  | zero => rw [ngen_zero, op_unit_right, Nat.add_zero]
  | succ _ hp => rw [ngen_succ, ←op_assoc, hp, ←Nat.add_assoc, ngen_succ]

theorem ngen_succ' [Monoid α] (a: α) (n: Nat): (n + 1) • a = a + (n • a) := by
  calc
    (n + 1) • a
    _ = (1 + n) • a := by rw [Nat.add_comm]
    _ = 1 • a + n • a := by rw [ngen_add]
    _ = a + n • a := by rw [ngen_one]

theorem ngen_inverses [Monoid α] {a b: α} (n: Nat) (h: a + b = 0): n • a + n • b = 0 := by
  induction n with
  | zero => simp [ngen_zero, op_unit_left]
  | succ p hp => rw [ngen_succ', ngen_succ, op_assoc, ←op_assoc (p • a), hp, op_unit_left, h]


theorem inverses_unique [Monoid M] {a b b': M}
  (h: inverses a b) (h': inverses a b'): b = b' := by
  simp_all [inverses_iff]
  calc
    b = b + 0        := by rw [op_unit_right]
    _ = b + (a + b') := by rw [h'.left]
    _ = (b + a) + b' := by rw [op_assoc]
    _ = 0 + b'       := by rw [h.right]
    _ = b'           := by rw [op_unit_left]


theorem left_right_inverse_eq [Monoid α] {a b c: α}
  (h₁: a + b = 0) (h₂: b + c = 0): a = c := by
  calc
    a = a + 0        := by rw [op_unit_right]
    _ = a + (b + c) := by rw [h₂]
    _ = (a + b) + c := by rw [op_assoc]
    _ = 0 + c       := by rw [h₁]
    _ = c           := by rw [op_unit_left]

-- On any type α the set of functions α → α is a monoid.
instance Monoid.endo (α: Type u): Monoid (α → α) := {
  op := λ f g ↦ g ∘ f
  unit := Function.id
  identity := by constructor <;> exact congrFun rfl
  assoc := by intro _ _ _ ; rfl
}

-- Lists form a monoid, the "free" monoid.
def Monoid.free (α: Type u): Monoid (List α) := {
  op := List.append
  unit := List.nil
  identity := by constructor <;> simp [LeftIdentity, RightIdentity]
  assoc := by intro; simp
}


class CommMonoid (α: Type u) extends Monoid α, CommMagma α


example: CommMonoid Nat := {
  op := Nat.add
  unit := 0
  identity := ⟨Nat.zero_add, Nat.add_zero⟩
  assoc := Nat.add_assoc
  comm := Nat.add_comm
}

example: CommMonoid Nat := {
  op := Nat.mul
  unit := 1
  identity := ⟨Nat.one_mul, Nat.mul_one⟩
  assoc := Nat.mul_assoc
  comm := Nat.mul_comm
}

example (α: Type u): CommMonoid (Set α) := {
  op := Set.union
  unit := Set.empty α
  identity := by exact Set.union_identity
  assoc := by exact Set.union_assoc
  comm := by exact Set.union_comm
}

example (α: Type u): CommMonoid (Set α) := {
  op := Set.inter
  unit := Set.full α
  identity := by exact Set.inter_identity
  assoc := by exact Set.inter_assoc
  comm := by exact Set.inter_comm
}


class Monoid.hom (M₁: Monoid α) (M₂: Monoid β) extends
  toPointedHom: Pointed.hom M₁.toPointed M₂.toPointed,
  toMagmaHom: Magma.hom M₁.toMagma M₂.toMagma

instance Monoid.hom.coeFun [M₁: Monoid α] [M₂: Monoid β]: CoeFun (Monoid.hom M₁ M₂) (λ _ ↦ α → β) := {
  coe f := f.map
}

class Monoid.sub (M: Monoid α) (S: Set α) extends
  toPointedSub: M.toPointed.sub S,
  toMagmaSub: M.toMagma.sub S

theorem Monoid.full_sub (M: Monoid α): M.sub (Set.full α) := {
  unit_mem := sorry
  op_closed := sorry
}

theorem Monoid.hom.image_sub {M₁: Monoid α} {M₂: Monoid β} (f: hom M₁ M₂): M₂.sub (Set.range f) := {
  unit_mem := (Pointed.hom.image_sub f.toPointedHom).unit_mem
  op_closed := (Magma.hom.image_sub f.toMagmaHom).op_closed
}

theorem Monoid.kernel_sub {M₁: Monoid α} {M₂: Monoid β} (f: hom M₁ M₂): M₁.sub f.kernel := {
  unit_mem := f.unit_preserving
  op_closed := by
    intro x y hx hy
    calc
      f (x + y)
      _ = f x + f y := by rw [f.op_preserving]
      _ = 0 + 0 := by rw [hx, hy]
      _ = 0 := by rw [op_unit_left]
}


def Monoid.opposite (M: Monoid α): Monoid α := {
  op := M.toMagma.opposite.op
  identity := ⟨identity.right, identity.left⟩
  assoc := by intro x y z; exact Eq.symm (assoc z y x)
}
