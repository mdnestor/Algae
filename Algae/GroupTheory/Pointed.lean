import Algae.SetTheory.Function
import Algae.SetTheory.Subset

variable {α: Type u} {β: Type v} {γ: Type w}



class Pointed (α: Type u) where
  unit: α



export Pointed (unit)
namespace Pointed
scoped instance [Pointed α]: Zero α := ⟨unit⟩
end Pointed
open Pointed



def Pointed.make (a: α): Pointed α := {
  unit := a
}



class Pointed.hom (P₁: Pointed α) (P₂: Pointed β) where
  map: α → β
  unit_preserving: map 0 = 0

instance Pointed.hom.coeFun [P₁: Pointed α] [P₂: Pointed β]: CoeFun (Pointed.hom P₁ P₂) (λ _ ↦ α → β) := {
  coe f := f.map
}

def Pointed.hom.id (P: Pointed α): hom P P := {
  map := Function.id
  unit_preserving := rfl
}

def Pointed.hom.comp {P₁: Pointed α} {P₂: Pointed β} {P₃: Pointed γ} (f: hom P₁ P₂) (g: hom P₂ P₃): hom P₁ P₃ := {
  map := g ∘ f
  unit_preserving := by simp [g.unit_preserving, f.unit_preserving]
}



class Pointed.sub (P: Pointed α) (S: Set α): Prop where
  unit_mem: 0 ∈ S

theorem Pointed.sub.full (P: Pointed α): P.sub Set.full := {
  unit_mem := trivial
}

theorem Pointed.hom.image_sub {P₁: Pointed α} {P₂: Pointed β} (f: hom P₁ P₂): P₂.sub (Set.range f) := {
  unit_mem := by
    rw [←f.unit_preserving]
    apply Set.range_mem
}

-- TODO: subpointed union, inter, subset

instance Pointed.product (P₁: Pointed α) (P₂: Pointed β): Pointed (α × β) := {
  unit := (0, 0)
}

def Pointed.hom.kernel {P₁: Pointed α} {P₂: Pointed β} (f: hom P₁ P₂): Set α :=
  λ a => f a = 0

theorem Pointed.kernel.sub {P₁: Pointed α} {P₂: Pointed β} (f: hom P₁ P₂): P₁.sub f.kernel := {
  unit_mem := f.unit_preserving
}
