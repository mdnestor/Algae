import Algae.SetTheory

variable {α: Type u}


class Monoid (α: Type u) extends Magma α, Pointed α where
  assoc: ∀ x y z, op (op x y) z = op x (op y z)
  id_left: ∀ x, op unit x = x
  id_right: ∀ x, op x unit = x



theorem add_assoc [Monoid α] (a b c: α): (a + b) + c = a + (b + c) := by
  exact Monoid.assoc a b c

theorem add_zero_left [Monoid α] (a: α): 0 + a = a := by
  exact Monoid.id_left a

theorem add_zero_right [Monoid α] (a: α): a + 0 = a := by
  exact Monoid.id_right a

theorem mul_assoc [Monoid α] (a b c: α): (a * b) * c = a * (b * c) := by
  apply add_assoc

theorem mul_one_left [Monoid α] (a: α): 1 * a = a := by
  apply add_zero_left

theorem mul_one_right [Monoid α] (a: α): a * 1 = a := by
  apply add_zero_right



class CommMonoid (α: Type u) extends Monoid α, CommMagma α



class Group (α: Type u) extends Monoid α where
  inv: α → α
  inv_left: ∀ x, op (inv x) x = unit
  inv_right: ∀ x, op x (inv x) = unit

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
  exact Group.inv_left a

theorem add_neg_right [Group α] (a: α): a + -a = 0 := by
  exact Group.inv_right a

theorem mul_inv_left [Group α] (a: α): a⁻¹ * a = 1 := by
  apply add_neg_left

theorem mul_inv_right [Group α] (a: α): a * a⁻¹ = 1 := by
  apply add_neg_right



class CommGroup (α: Type u) extends Group α, CommMonoid α

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
  rw [nmul_succ, nmul_zero, mul_eq, zero_eq, id_left]

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




theorem cancel_left [Group α] {a b c: α} (h: op a b = op a c): b = c := by
  repeat rw [←add_eq] at h
  calc b
    _ = (0: α) + b   := by rw [add_zero_left]
    _ = -a + a + b   := by rw [add_neg_left]
    _ = -a + (a + b) := by rw [add_assoc]
    _ = -a + (a + c) := by rw [h]
    _ = -a + a + c   := by rw [add_assoc]
    _ = 0 + c        := by rw [add_neg_left]
    _ = c            := by rw [add_zero_left]

theorem add_cancel_left [Group α] {a b c: α} (h: a + b = a + c): b = c := by
  exact cancel_left h

theorem mul_cancel_left [Group α] {a b c: α} (h: a * b = a * c): b = c := by
  exact cancel_left h

theorem inv_op [Group α] (a b: α): inv (op a b) = op (inv b) (inv a) := by
  sorry

theorem neg_plus [Group α] (a b: α): -(a + b) = -b + -a := by
  exact inv_op a b

theorem inv_unit [Group α]: inv (unit: α) = unit := by
  sorry

theorem inv_inv [Group α] (a: α): inv (inv a) = a := by
  sorry

theorem neg_neg [Group α] (a: α): -(-a) = a := by
  exact inv_inv a

class Ring (α: Type u) where
  add_struct: CommGroup α
  mul_struct: Monoid α
  distrib: Distributive mul_struct.op add_struct.op

def Ring.add [Ring α]: α → α → α :=
  Ring.add_struct.op

def Ring.mul [Ring α]: α → α → α :=
  Ring.mul_struct.op

def Ring.zero [Ring α]: α :=
  Ring.add_struct.unit

def Ring.one [Ring α]: α :=
  Ring.mul_struct.unit

def Ring.neg [Ring α]: α → α :=
  Ring.add_struct.inv

instance [Ring α]: Add α := {
  add := Ring.add
}

instance [Ring α]: Mul α := {
  mul := Ring.mul
}
instance [Ring α]: Zero α := {
  zero := Ring.add_struct.unit
}

instance [Ring α]: One α := {
  one := Ring.mul_struct.unit
}

instance [Ring α]: Neg α := {
  neg := Ring.neg
}

theorem Ring.add_assoc [Ring α] (a b c: α): a + b + c = a + (b + c) := by
  exact Ring.add_struct.assoc a b c

theorem Ring.add_zero_left [Ring α] (a: α): 0 + a = a := by
  exact Ring.add_struct.id_left a

theorem Ring.add_zero_right [Ring α] (a: α): a + 0 = a := by
  exact Ring.add_struct.id_right a

theorem Ring.add_neg_left [Ring α] (a: α): -a + a = 0 := by
  exact Ring.add_struct.inv_left a

theorem Ring.add_neg_right [Ring α] (a: α): a + -a = 0 := by
  exact Ring.add_struct.inv_right a

theorem Ring.mul_assoc [Ring α] (a b c: α): a * b * c = a * (b * c) := by
  exact Ring.mul_struct.assoc a b c

theorem Ring.mul_one_left [Ring α] (a: α): 1 * a = a := by
  exact Ring.mul_struct.id_left a

theorem Ring.mul_one_right [Ring α] (a: α): a * 1 = a := by
  exact Ring.mul_struct.id_right a

theorem Ring.distrib_left [Ring α] (a b c: α): a * (b + c) = (a * b) + (a * c) := by
  exact Ring.distrib.left a b c

theorem Ring.distrib_right [Ring α] (a b c: α): (a + b) * c = (a * c) + (b * c) := by
  exact Ring.distrib.right a b c

theorem Ring.mul_zero_left [Ring α] (a: α): 0 * a = 0 := by
  apply @add_cancel_left _ add_struct.toGroup (a := 0 * a)
  calc
    (0 * a) + (0 * a)
    _ = (0 + 0) * a := by rw [distrib_right]
    _ = 0 * a := by rw [add_zero_left]
    _ = 0 * a + 0 := by rw [add_zero_right]

class CommRing (α: Type u) extends Ring α where
  mul_comm: ∀ x y: α, x * y = y * x
