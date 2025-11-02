import Algae.Pointed
import Algae.Magma

variable {α: Type u}



class Monoid (α: Type u) extends Pointed α, Magma α where
  identity: Identity op unit
  assoc: Associative op


def Monoid.opposite (M: Monoid α): Monoid α := {
  op := M.toMagma.opposite.op
  identity := ⟨identity.right, identity.left⟩
  assoc := fun x y z => Eq.symm (assoc z y x)
}



theorem op_unit_left [Monoid α] (a: α): op unit a = a := by
  exact Monoid.identity.left a

theorem op_unit_right [Monoid α] (a: α): op a unit = a := by
  exact Monoid.identity.right a



theorem add_zero_left [Monoid A] (a: A): 0 + a = a := by
  apply op_unit_left

theorem add_zero_right [Monoid M] (a: M): a + 0 = a := by
  apply op_unit_right

theorem add_assoc [Monoid M] (a b c: M): a + b + c = a + (b + c) := by
  exact Monoid.assoc a b c



theorem mul_assoc [Monoid α] (a b c: α): (a * b) * c = a * (b * c) := by
  apply add_assoc

theorem mul_one_left [Monoid α] (a: α): 1 * a = a := by
  apply add_zero_left

theorem mul_one_right [Monoid α] (a: α): a * 1 = a := by
  apply add_zero_right

def inverses [Monoid α] (a b: α): Prop :=
  Inverses op a b unit

def inverses_iff [Monoid M] (a b: M): inverses a b ↔ a + b = 0 ∧ b + a = 0 := by
  rfl

def Monoid.nmul [Monoid α] (n: Nat) (a: α): α :=
  match n with
  | Nat.zero => unit
  | Nat.succ p => op (nmul p a) a

instance [Monoid α]: SMul Nat α := {
  smul := Monoid.nmul
}

-- Simple theorems about npow.
theorem nmul_zero' [Monoid α] (a: α): 0 • a = unit := by
  rfl


theorem nmul_zero [Monoid α] (a: α): 0 • a = (0: α) := by
  rfl

theorem nmul_succ [Monoid α] (a: α) (n: Nat): (n + 1) • a = (n • a) + a := by
  rfl

theorem nmul_one [Monoid α] (a: α): 1 • a = a := by
  rw [nmul_succ, nmul_zero, add_zero_left]

theorem nmul_two [Monoid α] (a: α): 2 • a = a + a := by
  rw [nmul_succ, nmul_one]

theorem nmul_add [Monoid α] (a: α) (m n: Nat): m • a + n • a = (m + n) • a := by
  induction n with
  | zero => rw [nmul_zero, add_zero_right, Nat.add_zero]
  | succ _ hp => rw [nmul_succ, ←add_assoc, hp, ←Nat.add_assoc, nmul_succ]

theorem nmul_succ' [Monoid α] (a: α) (n: Nat): (n + 1) • a = a + (n • a) := by
  calc
    (n + 1) • a
    _ = (1 + n) • a := by rw [Nat.add_comm]
    _ = 1 • a + n • a := by rw [nmul_add]
    _ = a + n • a := by rw [nmul_one]

theorem nmul_inverses [Monoid α] {a b: α} (n: Nat) (h: a + b = 0): n • a + n • b = 0 := by
  induction n with
  | zero => simp [nmul_zero, add_zero_left]
  | succ p hp => rw [nmul_succ', nmul_succ, add_assoc, ← add_assoc (p • a), hp, add_zero_left, h]


def npow [Monoid α] (a: α) (n: Nat): α :=
  match n with
  | Nat.zero => 1
  | Nat.succ p => npow a p * a

instance [Monoid α]: HPow α Nat α := {
  hPow := npow
}

theorem npow_zero [Monoid α] (a: α): a ^ 0 = (1: α) := by
  apply nmul_zero; exact a

theorem npow_succ [Monoid α] (a: α) (n: Nat): a ^ (n + 1) = a^n * a := by
  rfl

theorem npow_one [Monoid α] (a: α): a^1 = a := by
  apply nmul_one

theorem npow_two [Monoid α] (a: α): a^2 = a * a := by
  apply nmul_two

theorem inverses_unique [Monoid M] {a b b': M}
  (h: inverses a b) (h': inverses a b'): b = b' := by
  simp_all [inverses_iff]
  calc
    b = b + 0        := by rw [add_zero_right]
    _ = b + (a + b') := by rw [h'.left]
    _ = (b + a) + b' := by rw [add_assoc]
    _ = 0 + b'       := by rw [h.right]
    _ = b'           := by rw [add_zero_left]

macro "to_generic": tactic =>
  `(tactic| try simp [add_eq, zero_eq, mul_eq, one_eq])

macro "to_additive": tactic =>
  `(tactic| (to_generic; simp [←add_eq, ←zero_eq]))

macro "to_multiplicative": tactic =>
  `(tactic| (to_generic; simp [←mul_eq, ←one_eq]))

theorem left_right_inverse_eq [Monoid α] {a b c: α}
  (h₁: op a b = unit) (h₂: op b c = unit): a = c := by
  calc
    a = a + 0        := by rw [add_zero_right]
    _ = a + (b + c) := by to_generic; rw [h₂]
    _ = (a + b) + c := by rw [add_assoc]
    _ = 0 + c       := by to_generic; rw [h₁]
    _ = c           := by rw [add_zero_left]

-- On any type X the set of functions X → X is a monoid.
instance Endomonoid (M: Type u): Monoid (M → M) := {
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



class MonoidHom [Monoid α] [Monoid β] (f: α → β): Prop extends PointedHom f, MagmaHom f

class Submonoid [Monoid α] (S: Set α) extends Submagma S, Subpointed S



theorem Kernel.submonoid [Monoid α] [Monoid β] {f: α → β} (hf: MonoidHom f): Submonoid (Kernel f) := {
  unit_mem := hf.unit_preserving
  op_closed := by
    intro x y hx hy
    calc
      f (op x y)
      _ = op (f x) (f y) := by rw [hf.op_preserving]
      _ = op unit unit := by rw [hx, hy]
      _ = unit := by rw [Monoid.identity.left]
}
