import Algae.GroupTheory.Group
import Algae.GroupTheory.Action
import Algae.SetTheory.Function

variable {α: Type u} {β: Type v} {γ: Type w}

open Group

/-

Symmetric group, Cayley's theorem.

TODO:
- rewrite in terms of actions
- show G is isomorphic to a subgroup of the permutations.

-/

-- `Symm α` is the type of permutations on α,
-- consisting of (f, g) pairs with fg = gf = id.

abbrev Symm (α: Type u): Type u :=
  Invertible α α

-- The (left) symmetric group (with composition order (f, g) ↦ g;f = f ∘ g)

instance Group.symm.left (α: Type u): Group (Symm α) := {
  op := λ f g ↦ Invertible.comp g f
  unit := Invertible.id
  identity := by constructor <;> (intro; ext; repeat rfl)
  assoc := by (repeat intro); rfl
  inv := Invertible.inverse
  inverse := by
    constructor <;> (
      intro f
      simp [Invertible.inverse, Invertible.id, Invertible.comp]
    )
    apply f.id_left
    apply f.id_right
}

-- The (right) symmetric group (with composition order (f, g) ↦ f;g = g ∘ f)

instance Group.symm.right (α: Type u): Group (Symm α) := {
  op := λ f g ↦ Invertible.comp f g
  unit := Invertible.id
  identity := by constructor <;> (intro; ext; repeat rfl)
  assoc := by (repeat intro); rfl
  inv := Invertible.inverse
  inverse := by
    constructor <;> (
      intro f
      simp [Invertible.inverse, Invertible.id, Invertible.comp]
    )
    apply f.id_right
    apply f.id_left
}

/-

Cayley's theorem: every group is a subgroup of a symmetric group.
i.e. every group can be embedded in some symmetric group.

First we define the embedding from a group to the symmetric group on its elements
via left addition.

-/

def Group.symm_embed (G: Group α) (g: α): Symm α := {
  map := λ a ↦  g + a
  inv := λ a ↦ -g + a
  id_left := by
    ext a
    calc
      -g + (g + a)
      _ = -g + g + a := by rw [op_assoc]
      _ = 0 + a      := by rw [op_inv_left]
      _ = a          := by rw [op_unit_left]
  id_right := by
    ext a
    calc
       g + (-g + a)
       _ = g + -g + a := by rw [op_assoc]
       _ = 0 + a      := by rw [op_inv_right]
       _ = a          := by rw [op_unit_left]
}

-- Next we can show the embedding above is a group homomorphisms.

def Group.symm_embed_hom (G: Group α): hom G (Group.symm.right α) := sorry -- broke it :(

-- Finally we show the embedding is injective.

def Group.symm_unembed (G: Group α): Symm α → α :=
  λ π ↦ π.map 0

def Group.symm_embed_left_invertible (G: Group α): LeftInvertible α (Symm α) := {
  map := G.symm_embed
  inv := G.symm_unembed
  id_left := by ext; apply op_unit_right
}

-- The image of the embedding is a subgroup.

theorem Group.symm_embed_subgroup (G: Group α): (Group.symm.right α).sub (Set.range G.symm_embed) := by
  sorry
