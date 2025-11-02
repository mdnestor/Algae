import Algae.SetTheory

variable {α: Type u} {β: Type v} {γ: Type w}

class Pointed (α: Type u) where
  unit: α

export Pointed (unit)

-- local instance [Pointed α]: Zero α := {
--   zero := unit
-- }

-- instance [Pointed α]: One α := {
--   one := unit
-- }

-- theorem zero_eq [Pointed α]: (0: α) = unit := by
--   rfl

-- theorem one_eq [Pointed α]: (1: α) = unit := by
--   rfl



def Pointed.make (a: α): Pointed α := {
  unit := a
}

class PointedHom [Pointed α] [Pointed β] (f: α → β): Prop where
  unit_preserving: f unit = unit

theorem PointedHom.id [Pointed α]: PointedHom (@Function.id α) := {
  unit_preserving := rfl
}

theorem PointedHom.comp [Pointed α] [Pointed β] [Pointed γ] {f: α → β} {g: β → γ} (hf: PointedHom f) (hg: PointedHom g): PointedHom (g ∘ f) := {
  unit_preserving := by simp [hg.unit_preserving, hf.unit_preserving]
}



class Subpointed [Pointed α] (S: Set α): Prop where
  unit_mem: unit ∈ S

theorem Subpointed.full [Pointed α]: Subpointed (Set.full α) := {
  unit_mem := trivial
}

-- TODO: subpointed union, inter, subset

instance Pointed.product [Pointed α] [Pointed β]: Pointed (α × β) := {
  unit := (unit, unit)
}



def Kernel [Pointed β] (f: α → β): Set α :=
  λ a => f a = unit

theorem kernel_subpointed [Pointed α] [Pointed β] {f: α → β} (hf: PointedHom f): Subpointed (Kernel f) := {
  unit_mem := hf.unit_preserving
}
