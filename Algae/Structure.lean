import Algae.SetTheory

variable {α: Type u}

class Pointed (α: Type u) where
  unit: α

export Pointed (unit)

instance [Pointed α]: Zero α := {
  zero := unit
}



theorem zero_eq [Pointed α]: (0: α) = unit := by
  rfl

class Magma (α: Type u) where
  op: α → α → α

export Magma (op)

instance [Magma α]: Mul α := {
  mul := op
}

instance [Magma α]: Add α := {
  add := op
}

theorem mul_eq [Magma α] (a b: α): a * b = op a b := by
  rfl

theorem add_eq [Magma α] (a b: α): a + b = op a b := by
  rfl

class CommMagma (α: Type u) extends Magma α where
  comm: ∀ x y, op x y = op y x

export CommMagma (comm)

class Monoid (α: Type u) extends Magma α, Pointed α where
  assoc: ∀ x y z, op (op x y) z = op x (op y z)
  id_left: ∀ x, op unit x = x
  id_right: ∀ x, op x unit = x

export Monoid (assoc id_left id_right)

class CommMonoid (α: Type u) extends Monoid α, CommMagma α

class Group (α: Type u) extends Monoid α where
  inv: α → α
  inv_left: ∀ x, op (inv x) x = unit
  inv_right: ∀ x, op x (inv x) = unit

export Group (inv inv_left inv_right)

instance [Group α]: Neg α := {
  neg := inv
}

theorem neg_eq [Group α] (a: α): -a = inv a := by
  rfl

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

theorem Monoid.npow_two (M: Monoid α) (a: α): 2 • a = a * a := by
  rw [nmul_succ, nmul_one]

structure Submonoid (M: Monoid α) (S: Set α): Prop where
  unit_mem: 0 ∈ S
  add_closed {x y: α}: x ∈ S → y ∈ S → x * y ∈ S

structure Subgroup (G: Group α) (S: Set α): Prop extends Submonoid G.toMonoid S where
  inv_closed {x: α}: x ∈ S → -x ∈ S

theorem add_zero_left [Monoid α] (a: α): (0: α) + a = a := by
  exact Monoid.id_left a

theorem add_neg_left [Group α] (a: α): -a + a = 0 := by
  exact Group.inv_left a

theorem add_assoc [Monoid α] (x y z: α): (x + y) + z = x + (y + z) := by
  exact Monoid.assoc x y z

theorem add_cancel_left [Group α] (a b c: α) (h: a + b = a + c): b = c := by
  calc b
    _ = (0: α) + b   := by rw [add_zero_left]
    _ = -a + a + b   := by rw [add_neg_left]
    _ = -a + (a + b) := by rw [add_assoc]
    _ = -a + (a + c) := by rw [h]
    _ = -a + a + c   := by rw [add_assoc]
    _ = 0 + c        := by rw [add_neg_left]
    _ = c            := by rw [add_zero_left]

theorem mul_cancel_left [Group α] (a b c: α) (h: a * b = a * c): b = c := by
  repeat rw [mul_eq] at h
  repeat rw [←add_eq] at h
  exact add_cancel_left a b c h

class Ring (α: Type u) where
  add_struct: Group α
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
  apply @add_cancel_left _ add_struct (a := 0 * a)
  calc
    (0 * a) + (0 * a)
    _ = (0 + 0) * a := by rw [distrib_right]
    _ = 0 * a := by rw [add_zero_left]
    _ = 0 * a + 0 := by rw [add_zero_right]
