import Algae.Morphism
import Algae.Subobject

variable {α: Type u} {β: Type v}

def Kernel [Pointed β] (f: α → β): Set α :=
  λ a => f a = unit

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

theorem Kernel.subgroup [Group α] [Group β] {f: α → β} (hf: GroupHom f): Subgroup (Kernel f) := {
  unit_mem := (Kernel.submonoid hf.toMonoidHom).unit_mem
  op_closed := (Kernel.submonoid hf.toMonoidHom).op_closed
  inv_closed := by
    intro x hx
    calc
      f (inv x)
      _ = inv (f x) := by rw [hf.inv_preserving]
      _ = inv unit := by rw [hx]
      _ = unit := by rw [inv_unit]
}
