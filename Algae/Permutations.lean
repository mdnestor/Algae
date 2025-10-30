import Algae.Group

variable {α: Type u}

-- The set of permutations on α is all invertible functions α ↦ α.
def Permutation (α: Type u): Set (α → α) :=
  λ f ↦ Function.invertible f

-- The set of permutations on α forms a group.
noncomputable instance PermutationGroup (α: Type u): Group (Permutation α) := {
  add := λ f g ↦ ⟨g.val ∘ f.val, Function.invertible_comp f.property g.property⟩
  zero := ⟨id, Function.invertible_id⟩
  add_identity := by constructor <;> (intro; rfl)
  add_associative := by intro _ _ _; rfl
  neg := λ f ↦ ⟨f.property.choose, ⟨f, f.property.choose_spec.2, f.property.choose_spec.1⟩⟩
  add_inverse := by
    constructor <;> (intro ⟨f, hf⟩; simp; congr)
    exact hf.choose_spec.right
    exact hf.choose_spec.left
}

-- Fix a ∈ α. Define a permutation on α by x ↦ x + a.
def Group.element_map [Group α] (a: α): (α → α) :=
  λ x ↦ x + a

theorem Group.element_map_invertible [Group α] (a: α): Function.invertible (Group.element_map a) := by
  exists λ x ↦ x + -a
  constructor <;> (
    ext
    simp [
      element_map,
      add_associative,
      add_negative_left,
      add_negative_right,
      add_zero_right,
      Function.id
    ]
  )

theorem Group.element_map_bijective [Group α] (a: α): Function.Bijective (Group.element_map a) := by
  constructor
  · intro b b' h
    simp [element_map] at h
    exact add_cancel_right h
  · intro c
    simp [element_map]
    exists (c + -a)
    rw [add_associative, add_negative_left, add_zero_right]

-- Define a map α → (α → α) by a ↦ (x ↦ x + a).
def Group.element_permutation (α: Type u) [Group α]: α → Permutation α :=
  λ a ↦ ⟨element_map a, element_map_invertible a⟩

def Group.element_permutation_injective (α: Type u) [Group α]: Function.Injective (Group.element_permutation α) := by
  intro a b h
  simp [element_permutation] at h
  have h2: (element_map a) 0 = (element_map b) 0 := by exact congrFun h 0
  have ha: (element_map a) 0 = a := by simp [element_map]; rw [add_zero_left]
  have hb: (element_map b) 0 = b := by simp [element_map]; rw [add_zero_left]
  rw [ha, hb] at h2
  exact h2

theorem GroupHom.element_permutation_hom (α: Type u) [Group α]:
  GroupHom (Group.element_permutation α) := {
    add_preserving := by
      intros
      simp [Group.element_permutation]
      congr
      ext
      simp [Group.element_map]
      rw [add_associative]
    zero_preserving := by
      intros
      simp [Group.element_permutation]
      congr
      ext
      simp [Group.element_map]
      rw [add_zero_right]
    neg_preserving := by
      sorry
      -- intro a
      -- obtain ⟨a', ha'⟩ := Group.element_map_invertible a
      -- ext x
  }
