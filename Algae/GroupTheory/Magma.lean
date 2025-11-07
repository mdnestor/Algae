import Algae.SetTheory.Function
import Algae.SetTheory.Subset

variable {α: Type u}

class Magma (α: Type u) where
  op: α → α → α

export Magma (op)

-- instance [Magma α]: Add α := {
--   add := op
-- }

-- instance [Magma α]: Mul α := {
--   mul := op
-- }

-- theorem add_eq [Magma α] (a b: α): a + b = op a b := by
--   rfl

-- theorem mul_eq [Magma α] (a b: α): a * b = op a b := by
--   rfl

class CommMagma (α: Type u) extends Magma α where
  comm: ∀ x y, op x y = op y x

theorem op_comm [CommMagma α] (a b: α): op a b = op b a := by
  exact CommMagma.comm a b

-- theorem mul_comm [CommMagma α] (a b: α): a * b = b * a := by
--   apply add_comm

def Magma.opposite (M: Magma α): Magma α := {
  op := flip op
}

def CommMagma.opposite (M: CommMagma α): CommMagma α := {
  op := M.toMagma.opposite.op
  comm := by intro x y; exact comm y x
}



class MagmaHom [Magma α] [Magma β] (f: α → β): Prop where
  op_preserving: ∀ a b: α, f (op a b) = op (f a) (f b)

theorem MagmaHom.id (α: Type u) [Magma α]: MagmaHom (@Function.id α) := by
  sorry

theorem MagmaHom.comp [Magma α] [Magma β] [Magma γ]
  {f: α → β} {g: β → γ} (hf: MagmaHom f) (hg: MagmaHom g)
  : MagmaHom (g ∘ f) := by
  sorry



class Submagma [Magma α] (S: Set α): Prop where
  op_closed: ∀ a b, a ∈ S → b ∈ S → op a b ∈ S
