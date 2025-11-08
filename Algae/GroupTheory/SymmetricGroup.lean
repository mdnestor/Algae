/-

Symmetric group, Cayley's theorem.

TODO:
- `Symm.embed_left`, `Symm.embed_right` are group actions and `Symm.embed_left_hom`, `Symm.embed_right_hom` are special cases of group actions being group homomorphisms to the symmetric group.

-/

import Algae.GroupTheory.Group
import Algae.GroupTheory.Action

variable {α: Type u}

local instance [Monoid α]:  Add α := ⟨op⟩
local instance [Monoid α]: Zero α := ⟨unit⟩
local instance  [Group α]:  Neg α := ⟨inv⟩
local instance  [Group α]:  Sub α := ⟨invop⟩

-- A structure for invertible functions. TODO: move elsewhere?
@[ext] structure InvertiblePair (X: Type u) (Y: Type v) where
  map: X → Y
  inv: Y → X

@[ext] structure LeftInvertible (X: Type u) (Y: Type v) extends InvertiblePair X Y where
  id_left: inv ∘ map = id

@[ext] structure RightInvertible (X: Type u) (Y: Type v) extends InvertiblePair X Y where
  id_right: map ∘ inv = id

@[ext] structure Invertible (X: Type u) (Y: Type v) extends LeftInvertible X Y, RightInvertible X Y

def Invertible.id {X: Type u}: Invertible X X := {
  map := Function.id
  inv := Function.id
  id_left := sorry
  id_right := sorry
}

def Invertible.inverse {X Y: Type u} (f: Invertible X Y): Invertible Y X := {
  map := f.inv
  inv := f.map
  id_left := sorry
  id_right := sorry
}

def Invertible.comp {X Y Z: Type u} (f: Invertible X Y) (g: Invertible Y Z): Invertible X Z := {
  map := g.map ∘ f.map
  inv := f.inv ∘ g.inv
  id_left := sorry
  id_right := sorry
}

abbrev Symm (α: Type u): Type u :=
  Invertible α α

instance Symm.group (α: Type u): Group (Symm α) := {
  op := flip Invertible.comp
  unit := Invertible.id
  identity := by constructor <;> (intro; ext; repeat rfl)
  assoc := by (repeat intro); rfl
  inv := Invertible.inverse
  inverse := by
    constructor <;> (
      intro f
      simp [Invertible.inverse, Invertible.id, flip, Invertible.comp]
    )
    apply f.id_left
    apply f.id_right
}

/-

Cayley's theorem: every group is a subgroup of a symmetric group.
i.e. every group can be embedded in some symmetric group.

-/

-- First we define the mapping from a group to the symmetric group on its elements
-- given by left/right operation respectively.
def Symm.embed_left (G: Group α) (g: α): Symm α := {
  map := fun a ↦ g + a
  inv := fun a ↦ -g + a
  id_left := by
     ext a
     simp
     rw [←op_assoc]
     rw [op_inv_left]
     rw [op_unit_left]
  id_right := sorry
}

def Symm.embed_right (G: Group α) (g: α): Symm α := {
  map := fun a ↦ a + g
  inv :=fun a ↦ a + -g
  id_left := by
     ext a
     simp
     rw [op_assoc]
     rw [op_inv_right]
     rw [op_unit_right]
  id_right := sorry
}

-- Next we can show the mappings above are group homomorphisms.
theorem Symm.embed_left_hom [G: Group α]: GroupHom (Symm.embed_left G) := {
  unit_preserving := by
    ext a
    · exact op_unit_left a
    · calc
        -0 + a
        _ = 0 + a := by rw [inv_unit]
        _ = a := by rw [op_unit_left]
  op_preserving := by
    intro g₁ g₂; ext a
    · calc
      (g₁ + g₂) + a
      _ = g₁ + (g₂ + a) := by rw [op_assoc]
    · calc
      -(g₁ + g₂) + a
      _ = (-g₂ + -g₁) + a := by rw [inv_op]
      _ = -g₂ + (-g₁ + a) := by rw [op_assoc]
  inv_preserving := by
    intro g; ext a
    · rfl
    · calc
      -(-g) + a
      _ = g + a := by rw [inv_inv]
}

-- TODO: there is an opposite that needs to be inserted somewhere?
theorem Symm.embed_right_hom [G: Group α]: GroupHom (Symm.embed_right G) := {
  unit_preserving := by
    ext a
    · apply op_unit_right
    · to_additive
      simp [Symm.embed_right, inv_unit, op_unit_right]
      rfl
  op_preserving := by
    intro g₁ g₂
    ext a
    to_additive
    simp [Symm.embed_right]
    calc
      a + (g₁ + g₂)
      _ = (a + g₂) + g₁ := by sorry
    sorry
  inv_preserving := by
    sorry
}

def Symm.unembed [Group α]: Symm α → α :=
  λ π ↦ π.map 0

def Symm.embed_left_invertible [G: Group α]: LeftInvertible α (Symm α) := {
  map := Symm.embed_left G
  inv := Symm.unembed
  id_left := by
    ext a
    exact op_unit_right a
}

-- The image of `Symm.embed_left` is a subgroup of `Symm α`.
example [G: Group α]: Subgroup (Set.range (Symm.embed_left G)) := by
  exact Subgroup.image_hom Symm.embed_left_hom
