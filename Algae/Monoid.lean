import Algae.Magma
import Algae.PointedSet

variable {M : Type u}

class UnitalMagma (M : Type u) extends Magma M, PointedSet M where
  add_identity: Identity add 0

theorem add_zero_left [UnitalMagma M] (a: M): 0 + a = a := by
  exact UnitalMagma.add_identity.left a

theorem add_zero_right [UnitalMagma M] (a: M): a + 0 = a := by
  exact UnitalMagma.add_identity.right a

def UnitalMagma.inverses [UnitalMagma M] (a b: M): Prop :=
  Inverses Add.add a b 0

def UnitalMagma.inverses_iff [UnitalMagma M] (a b: M):
  inverses a b ↔ a + b = 0 ∧ b + a = 0 := by
  rfl

/-

In an additive unital magma we can "multiply" by natural numers a la `n • a` by

0 • a = 0
1 • a = a
2 • a = a + a
3 • a = (a + a) + a
4 • a = ((a + a) + a) + a (notice we don't have associavitiy)

etc...

-/

def UnitalMagma.smul [UnitalMagma M] (n: Nat) (a: M): M :=
  match n with
  | Nat.zero => 0
  | Nat.succ p => smul p a + a

instance [UnitalMagma M]: SMul Nat M := {
  smul := UnitalMagma.smul
}

-- Simple theorems about npow.
theorem UnitalMagma.smul_zero [UnitalMagma M] (a: M): 0 • a = 0 := by
  rfl

theorem UnitalMagma.smul_succ [UnitalMagma M] (a: M) (n: Nat): n.succ • a = n • a + a := by
  rfl

theorem UnitalMagma.smul_one [UnitalMagma M] (a: M): 1 • a = a := by
  rw [smul_succ, smul_zero]
  exact add_identity.left a

theorem UnitalMagma.npow_two [UnitalMagma M] (a: M): 2 • a = a + a := by
  rw [smul_succ, smul_one]

class Monoid (M: Type u) extends UnitalMagma M, AssociativeMagma M

theorem inverses_unique [Monoid M] {a b b': M}
  (h: UnitalMagma.inverses a b) (h': UnitalMagma.inverses a b'): b = b' := by
  simp_all [UnitalMagma.inverses_iff]
  calc
    b = b + 0        := by rw [add_zero_right]
    _ = b + (a + b') := by rw [h'.left]
    _ = (b + a) + b' := by rw [add_associative]
    _ = 0 + b'       := by rw [h.right]
    _ = b'           := by rw [add_zero_left]

-- On any type X the set of functions X → X is a monoid.
def Endomonoid (M : Type u) : Monoid (M → M) := {
  add := λ f g ↦ g ∘ f
  zero := Function.id
  add_identity := by constructor <;> exact congrFun rfl
  add_associative := by intro _ _ _ ; rfl
}

-- List M is a monoid.
def FreeMonoid (M : Type u) : Monoid (List M) := {
  add := List.append
  zero := List.nil
  add_identity := by constructor <;> (simp [LeftIdentity, RightIdentity]; rfl)
  add_associative := by intro; simp
}

class CommutativeMonoid (M : Type u) extends Monoid M, CommutativeMagma M

example (M : Type u) : CommutativeMonoid (Set M) := {
  add := Set.union
  zero := Set.empty M
  add_identity := by exact Set.union_identity
  add_associative := by exact Set.union_assoc
  add_commutative := by exact Set.union_comm
}

example (M : Type u) : CommutativeMonoid (Set M) := {
  add := Set.inter
  zero := Set.full M
  add_identity := by exact Set.inter_identity
  add_associative := by exact Set.inter_assoc
  add_commutative := by exact Set.inter_comm
}

example: CommutativeMonoid Nat := {
  add := Nat.add
  zero := 0
  add_identity := by constructor; simp [LeftIdentity]; exact congrFun rfl
  add_associative := by exact Nat.add_assoc
  add_commutative := by exact Nat.add_comm
}

example: CommutativeMonoid Nat := {
  add := Nat.mul
  zero := 1
  add_identity := ⟨Nat.one_mul, Nat.mul_one⟩
  add_associative := by exact Nat.mul_assoc
  add_commutative := by exact Nat.mul_comm
}

-- example  (M: UnitalMagma M) (a: M): CommutativeMonoid (Subtype (Set.range (fun n: Nat ↦ M.npow a n))) := {
--   add := sorry
--   zero := sorry
--   identity := sorry
--   associative := sorry
--   commutative := sorry
-- }


class UnitalMulMagma (M : Type u) extends MulMagma M, PointedMulSet M where
  identity: Identity mul 1

theorem mul_one_left [UnitalMulMagma M] (a: M): 1 * a = a := by
  exact UnitalMulMagma.identity.left a

theorem mul_one_right [UnitalMulMagma M] (a: M): a * 1 = a := by
  exact UnitalMulMagma.identity.right a

def UnitalMulMagma.inverses [UnitalMulMagma M] (a b: M): Prop :=
  Inverses Mul.mul a b 1

def UnitalMulMagma.inverses_iff [UnitalMulMagma M] (a b: M):
  inverses a b ↔ a * b = 1 ∧ b * a = 1 := by
  rfl

def UnitalMulMagma.npow [UnitalMulMagma M] (a: M) (n: Nat): M :=
  match n with
  | Nat.zero => 1
  | Nat.succ p => npow a p * a

instance [UnitalMulMagma M]: HPow M Nat M := {
  hPow := UnitalMulMagma.npow
}

-- Simple theorems about npow.
theorem npow_zero [UnitalMulMagma M] (a: M): a ^ 0 = 1 := by
  rfl

theorem npow_succ [UnitalMulMagma M] (a: M) (n: Nat): a ^ n.succ = a ^ n * a := by
  rfl

theorem npow_one [UnitalMulMagma M] (a: M): a ^ 1 = a := by
  rw [npow_succ, npow_zero]
  exact mul_one_left a

theorem npow_two [UnitalMulMagma M] (a: M): a ^ 2 = a * a := by
  rw [npow_succ, npow_one]

class MulMonoid (M: Type u) extends UnitalMulMagma M, AssociativeMulMagma M

-- theorem inverses_unique [M: Monoid M] {a b b': M}
--   (h: UnitalMagma.inverses a b) (h': UnitalMagma.inverses a b'): b = b' := by
--   simp_all [UnitalMagma.inverses_iff]
--   calc
--     b = b + 0        := by rw [add_zero_right]
--     _ = b + (a + b') := by rw [h'.left]
--     _ = (b + a) + b' := by rw [add_associative]
--     _ = 0 + b'       := by rw [h.right]
--     _ = b'           := by rw [add_zero_left]

class CommutativeMulMonoid (M : Type u) extends MulMonoid M, CommutativeMulMagma M
