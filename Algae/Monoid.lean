import Algae.Pointed
import Algae.Magma

variable {α: Type u}



class Monoid (α: Type u) extends Pointed α, Magma α where
  identity: Identity op unit
  assoc: Associative op



theorem add_zero_left [Monoid A] (a: A): 0 + a = a := by
  exact Monoid.identity.left a

theorem add_zero_right [Monoid M] (a: M): a + 0 = a := by
  exact Monoid.identity.right a

theorem add_assoc [Monoid M] (a b c: M): a + b + c = a + (b + c) := by
  exact Monoid.assoc a b c



theorem mul_assoc [Monoid α] (a b c: α): (a * b) * c = a * (b * c) := by
  apply add_assoc

theorem mul_one_left [Monoid α] (a: α): 1 * a = a := by
  apply add_zero_left

theorem mul_one_right [Monoid α] (a: α): a * 1 = a := by
  apply add_zero_right



def Monoid.inverses [Monoid M] (a b: M): Prop :=
  Inverses Add.add a b 0

def Monoid.inverses_iff [Monoid M] (a b: M):
  inverses a b ↔ a + b = 0 ∧ b + a = 0 := by
  rfl




def Monoid.nmul [Monoid α] (n: Nat) (a: α): α :=
  match n with
  | Nat.zero => unit
  | Nat.succ p => op (nmul p a) a

instance [Monoid α]: SMul Nat α := {
  smul := Monoid.nmul
}

-- Simple theorems about npow.
theorem Monoid.nmul_zero (M: Monoid α) (a: α): 0 • a = (0: α) := by
  rfl

theorem Monoid.nmul_succ (M: Monoid α) (a: α) (n: Nat): (n + 1) • a = (n • a) * a := by
  rfl

theorem Monoid.nmul_one (M: Monoid α) (a: α): 1 • a = a := by
  rw [nmul_succ, nmul_zero, mul_eq, zero_eq]
  sorry

theorem Monoid.nmul_two (M: Monoid α) (a: α): 2 • a = a * a := by
  rw [nmul_succ, nmul_one]



def Monoid.npow [Monoid α] (a: α) (n: Nat): α :=
  match n with
  | Nat.zero => 1
  | Nat.succ p => npow a p * a

instance [Monoid α]: HPow α Nat α := {
  hPow := Monoid.npow
}

theorem Monoid.npow_zero (M: Monoid α) (a: α): a ^ 0 = (1: α) := by
  apply Monoid.nmul_zero; exact a

theorem Monoid.npow_succ (M: Monoid α) (a: α) (n: Nat): a ^ (n + 1) = a^n * a := by
  sorry

theorem Monoid.npow_one (M: Monoid α) (a: α): a^1 = a := by
  apply Monoid.nmul_one

theorem Monoid.npow_two (M: Monoid α) (a: α): a^2 = a * a := by
  apply Monoid.nmul_two



theorem inverses_unique [Monoid M] {a b b': M}
  (h: Monoid.inverses a b) (h': Monoid.inverses a b'): b = b' := by
  simp_all [Monoid.inverses_iff]
  calc
    b = b + 0        := by rw [add_zero_right]
    _ = b + (a + b') := by rw [h'.left]
    _ = (b + a) + b' := by rw [add_assoc]
    _ = 0 + b'       := by rw [h.right]
    _ = b'           := by rw [add_zero_left]

-- On any type X the set of functions X → X is a monoid.
def Endomonoid (M: Type u): Monoid (M → M) := {
  op := λ f g ↦ g ∘ f
  unit := Function.id
  identity := by constructor <;> exact congrFun rfl
  assoc := by intro _ _ _ ; rfl
}

-- List M is a monoid.
def FreeMonoid (M : Type u) : Monoid (List M) := {
  op := List.append
  unit := List.nil
  identity := by constructor <;> simp [LeftIdentity, RightIdentity]
  assoc := by intro; simp
}


class CommMonoid (A : Type u) extends Monoid A, CommMagma A


example (M: Type u): CommMonoid (Set M) := {
  op := Set.union
  unit := Set.empty M
  identity := by exact Set.union_identity
  assoc := by exact Set.union_assoc
  comm := by exact Set.union_comm
}

example (M: Type u): CommMonoid (Set M) := {
  op := Set.inter
  unit := Set.full M
  identity := by exact Set.inter_identity
  assoc := by exact Set.inter_assoc
  comm := by exact Set.inter_comm
}

example: CommMonoid Nat := {
  op := Nat.add
  unit := 0
  identity := by constructor; simp [LeftIdentity]; exact congrFun rfl
  assoc := by exact Nat.add_assoc
  comm := by exact Nat.add_comm
}

example: CommMonoid Nat := {
  op := Nat.mul
  unit := 1
  identity := ⟨Nat.one_mul, Nat.mul_one⟩
  assoc := by exact Nat.mul_assoc
  comm := by exact Nat.mul_comm
}
