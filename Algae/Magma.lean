import Algae.SetTheory

variable {α: Type u}

class Magma (α: Type u) where
  op: α → α → α

export Magma (op)

instance [Magma α]: Add α := {
  add := op
}

instance [Magma α]: Mul α := {
  mul := op
}

theorem add_eq [Magma α] (a b: α): a + b = op a b := by
  rfl

theorem mul_eq [Magma α] (a b: α): a * b = op a b := by
  rfl

class CommMagma (α: Type u) extends Magma α where
  comm: ∀ x y, op x y = op y x

theorem add_comm [CommMagma α] (a b: α): a + b = b + a := by
  exact CommMagma.comm a b

theorem mul_comm [CommMagma α] (a b: α): a * b = b * a := by
  apply add_comm
