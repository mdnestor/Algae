import Algae.SetTheory
import Algae.Group
import Algae.Cat

variable {α: Type u} {β: Type v} {γ: Type w}

class PointedHom [Pointed α] [Pointed β] (f: α → β): Prop where
  unit_preserving: f unit = unit

class MagmaHom [Magma α] [Magma β] (f: α → β): Prop where
  op_preserving: ∀ a b: α, f (op a b) = op (f a) (f b)

class MonoidHom [Monoid α] [Monoid β] (f: α → β): Prop extends PointedHom f, MagmaHom f

class GroupHom [Group α] [Group β] (f: α → β): Prop extends MonoidHom f where
  inv_preserving: ∀ a, f (inv a) = inv (f a)



theorem MagmaHom.id (α: Type u) [Magma α]: MagmaHom (@Function.id α) := by
  sorry

theorem MagmaHom.comp [Magma α] [Magma β] [Magma γ]
  {f: α → β} {g: β → γ} (hf: MagmaHom f) (hg: MagmaHom g)
  : MagmaHom (g ∘ f) := by
  sorry



-- Example attemmpt fitting into a cat.

structure MagmaObj where
  carrier: Type u
  magma: Magma carrier

structure MagmaObjHom (M₁ M₂: MagmaObj) where
  map: M₁.carrier → M₂.carrier
  isHom: @MagmaHom _ _ M₁.magma M₂.magma map

def MagmaObjHom.id (M: MagmaObj): MagmaObjHom M M := {
  map := Function.id
  isHom := @MagmaHom.id M.carrier M.magma
}

-- The category of Magmas.
def MagmaCat: Cat.{u + 1} := {
  obj := MagmaObj
  hom := MagmaObjHom
  id := @MagmaObjHom.id
  comp := sorry
  id_left := sorry
  id_right := sorry
  associative := sorry
}
