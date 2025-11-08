import Algae.SetTheory.Function
import Algae.SetTheory.Subset

variable {α: Type u} {β: Type v} {γ: Type w}

/-

A magma is just a set with an operation.

-/

class Magma (α: Type u) where
  op: α → α → α

class CommMagma (α: Type u) extends Magma α where
  comm: Commutative op




export Magma (op)
namespace Magma
scoped instance [Magma α]: Add α := ⟨op⟩
end Magma

open Magma



theorem op_comm [CommMagma α] (a b: α): a + b = b + a := by
  exact CommMagma.comm a b



-- A magma homomorphism preserves the operation.

class Magma.hom (M₁: Magma α) (M₂: Magma β) where
  map: α → β
  op_preserving: ∀ a b, map (a + b) = map a + map b


def Magma.hom.id (M: Magma α): hom M M := {
  map := Function.id
  op_preserving := by intros; rfl
}

def Magma.hom.comp {M₁: Magma α} {M₂: Magma β} {M₃: Magma γ} (f: hom M₁ M₂) (g: hom M₂ M₃): hom M₁ M₃ := {
  map := g.map ∘ f.map
  op_preserving := by intros; simp [f.op_preserving, g.op_preserving]
}


-- A submagma is a subset which is closed under the operation.

class Magma.sub (M: Magma α) (S: Set α): Prop where
  op_closed: ∀ a b, a ∈ S → b ∈ S → a + b ∈ S

-- The image of a magma homomorphism is a submagma.

theorem Magma.hom.image_sub {M₁: Magma α} {M₂: Magma β} (f: hom M₁ M₂): Magma.sub M₂ (Set.range f.map) := {
  op_closed := by
    intro _ _ ⟨a₁, ha₁⟩ ⟨a₂, ha₂⟩
    rw [←ha₁, ←ha₂, ←f.op_preserving]
    apply Set.range_mem
}

-- The opposite magma has the flipped operation.

def Magma.opposite (M: Magma α): Magma α := {
  op := flip op
}

-- If a magma is commutative, so is its opposite.

def CommMagma.opposite (M: CommMagma α): CommMagma α := {
  op := (Magma.opposite M.toMagma).op
  comm := by intro x y; exact comm y x
}
