import Algae.Magma
import Algae.PointedSet

variable {α : Type u}

class UnitalMagma (α : Type u) extends Magma α, PointedSet α where
  identity : Identity op unit

theorem UnitalMagma.identity_left {M : UnitalMagma α} : LeftIdentity M.op M.unit := by
  exact M.identity.left

theorem UnitalMagma.identity_right {M : UnitalMagma α} : RightIdentity M.op M.unit := by
  exact M.identity.right

def UnitalMagma.inverses {M : UnitalMagma α} (a b : α) : Prop :=
  Inverses M.op a b M.unit ∧ Inverses M.op b a M.unit

/-

In a unital magma we can define natural numbers powers a^n by

a^0 = 1
a^1 = a
a^2 = a * a
a^3 = (a * a) * a
a^4 = ((a * a) * a) * a  (notice we don't have associavitiy)

etc...

-/

def UnitalMagma.npow {M: UnitalMagma α} (a: α) (n: Nat): α :=
  match n with
  | Nat.zero => M.unit
  | Nat.succ p => M.op (M.npow a p) a

-- Simple theorems about npow.
theorem UnitalMagma.npow_zero (M: UnitalMagma α) (a: α): M.npow a 0 = M.unit := by
  rfl

theorem UnitalMagma.npow_succ (M: UnitalMagma α) (a: α) (n: Nat): M.npow a n.succ = M.op (M.npow a n) a := by
  rfl

theorem UnitalMagma.npow_one (M: UnitalMagma α) (a: α): M.npow a 1 = a := by
  rw [npow_succ, npow_zero]
  exact identity.left a

theorem UnitalMagma.npow_two (M: UnitalMagma α) (a: α): M.npow a 2 = M.op a a := by
  rw [npow_succ, npow_one]

class Monoid (α: Type u) extends UnitalMagma α, AssociativeMagma α

theorem inverse_unique {M: Monoid α} {a b b': α}
  (h: M.inverses a b) (h': M.inverses a b'): b = b' := by
  calc
    b = M.op M.unit b      := by rw [M.identity_left]
    _ = M.op (M.op b' a) b := by rw [h'.right]
    _ = M.op b' (M.op a b) := by rw [M.associative]
    _ = M.op b' M.unit     := by rw [h.left]
    _ = b'                 := by rw [M.identity.right b']

-- On any type X the set of functions X → X is a monoid.
def Endomonoid (α : Type u) : Monoid (α → α) := {
  op := λ f g ↦ g ∘ f
  unit := Function.id
  identity := by constructor <;> exact congrFun rfl
  associative := by intro _ _ _ ; rfl
}

-- List α is a monoid.
def FreeMonoid (α : Type u) : Monoid (List α) := {
  op := List.append
  unit := List.nil
  identity := by constructor <;> simp [LeftIdentity, RightIdentity]
  associative := by intro; simp
}

class CommutativeMonoid (α : Type u) extends Monoid α, CommutativeMagma α

example (α : Type u) : CommutativeMonoid (Set α) := {
  op := Set.union
  unit := Set.empty α
  identity := by exact Set.union_identity
  associative := by exact Set.union_assoc
  commutative := by exact Set.union_comm
}

example (α : Type u) : CommutativeMonoid (Set α) := {
  op := Set.inter
  unit := Set.full α
  identity := by exact Set.inter_identity
  associative := by exact Set.inter_assoc
  commutative := by exact Set.inter_comm
}

example: CommutativeMonoid Nat := {
  op := Nat.add
  unit := 0
  identity := by constructor; simp [LeftIdentity]; exact congrFun rfl
  associative := by exact Nat.add_assoc
  commutative := by exact Nat.add_comm
}

example: CommutativeMonoid Nat := {
  op := Nat.mul
  unit := 1
  identity := by constructor; simp [LeftIdentity]; simp [RightIdentity]
  associative := by exact Nat.mul_assoc
  commutative := by exact Nat.mul_comm
}

example  (M: UnitalMagma α) (a: α): CommutativeMonoid (Subtype (Set.range (fun n: Nat ↦ M.npow a n))) := {
  op := sorry
  unit := sorry
  identity := sorry
  associative := sorry
  commutative := sorry
}
