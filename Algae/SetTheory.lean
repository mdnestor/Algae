import Algae.Basic

variable {α: Type u} {β: Type v}

def Function.id {α: Type u}: α → α :=
  λ x ↦ x

def Function.Bijective  (f: α → β): Prop :=
  Injective f ∧ Surjective f

def Set (α: Type u): Type u :=
  α → Prop

instance (α: Type u): CoeSort (Set α) (Type u) := {
  coe := Subtype
}

def Set.empty (α: Type u): Set α :=
  λ _ ↦ False

def Set.full (α: Type u): Set α :=
  λ _ ↦ True

instance: Membership α (Set α) := {
  mem := λ A a ↦ A a
}

instance: HasSubset (Set α) := {
  Subset := λ A B ↦ ∀ x, A x → B x
}

instance: EmptyCollection (Set α) := {
  emptyCollection := Set.empty α
}

def Set.inter (A B: Set α): Set α :=
  λ x ↦ x ∈ A ∧ x ∈ B

instance: Inter (Set α) := {
  inter := Set.inter
}

def Set.union (A B: Set α): Set α :=
  λ x ↦ x ∈ A ∨ x ∈ B

instance: Union (Set α) := {
  union := Set.inter
}

def Set.compl (A: Set α): Set α :=
  λ x ↦ x ∉ A

def Set.subtype (A: Set α): Type u :=
  Σ a, PLift (a ∈ A)

theorem Set.union_left_identity: LeftIdentity Set.union (Set.empty α) := by
  intro
  funext
  simp [Set.union]
  exact or_iff_right id

theorem Set.union_right_identity: RightIdentity Set.union (Set.empty α) := by
  intro
  funext
  simp [Set.union]
  exact or_iff_left id

theorem Set.union_identity: Identity Set.union (Set.empty α) := by
  exact ⟨Set.union_left_identity, Set.union_right_identity⟩

theorem Set.union_assoc: Associative (@Set.union α) := by
  intro A B C
  funext x
  simp [Set.union]
  constructor
  · intro h
    cases h with
    | inl h =>
      cases h with
      | inl h => exact Or.inl h
      | inr h => exact Or.inr (Or.inl h)
    | inr h => exact Or.inr (Or.inr h)
  · intro h
    cases h with
    | inl h => exact Or.inl (Or.inl h)
    | inr h =>
      cases h with
      | inl h => exact Or.inl (Or.inr h)
      | inr h => exact Or.inr h

theorem Set.union_comm: Commutative (@Set.union α) := by
  intro A B
  funext x
  simp [Set.union]
  exact Or.comm

theorem Set.inter_identity: Identity Set.inter (Set.full α) := by
  constructor
  · intro A
    funext x
    simp [Set.inter]
    constructor
    · intro h
      exact h.right
    · intro h
      exact ⟨trivial, h⟩
  · intro A
    funext x
    simp [Set.inter]
    constructor
    · intro h
      exact h.left
    · intro h
      exact ⟨h, trivial⟩

theorem Set.inter_assoc: Associative (@Set.inter α) := by
  intro A B C
  funext x
  simp [Set.inter]
  constructor
  · intro ⟨⟨ha, hb⟩, hc⟩
    exact ⟨ha, ⟨hb, hc⟩⟩
  · intro ⟨ha, ⟨hb, hc⟩⟩
    exact ⟨⟨ha, hb⟩, hc⟩

theorem Set.inter_comm: Commutative (@Set.inter α) := by
  intro A B
  funext x
  simp [Set.inter]
  constructor <;> (intro h; exact And.symm h;)

-- This is very ugly! :)
-- But I don't know how to simplify it
example: Distributive (@Set.union α) (@Set.inter α) := by
  constructor
  · intro A B C
    funext x
    simp [Set.union, Set.inter]
    constructor
    · intro h
      cases h with
      | inl h => exact ⟨Or.inl h, Or.inl h⟩
      | inr h => exact ⟨Or.inr h.left, Or.inr h.right⟩
    · intro ⟨hab, hac⟩
      by_cases h : x ∈ A
      · exact Or.inl h
      · have hb : x ∈ B := by cases hab with
        | inl ha => contradiction
        | inr hb => exact hb
        have hc : x ∈ C := by cases hac with
        | inl ha => contradiction
        | inr hc => exact hc
        exact Or.inr ⟨hb, hc⟩
  · intro A B C
    funext x
    simp
    constructor
    · intro h
      cases h with
      | inl h => exact ⟨Or.inl h.left, Or.inl h.right⟩
      | inr h => exact ⟨Or.inr h, Or.inr h⟩
    · intro ⟨hac, hbc⟩
      by_cases h : x ∈ C
      · exact Or.inr h
      · have ha : x ∈ A := by cases hac with
        | inl ha => exact ha
        | inr hc => contradiction
        have hb : x ∈ B := by cases hbc with
        | inl hb => exact hb
        | inr hc => contradiction
        exact Or.inl ⟨ha, hb⟩

example: Distributive (@Set.inter α) (@Set.union α) := by
  constructor
  · intro A B C
    funext x
    simp
    constructor
    · intro ⟨ha, hbc⟩
      by_cases hb : x ∈ B
      · exact Or.inl ⟨ha, hb⟩
      · have hc : x ∈ C := by cases hbc with
        | inl hb' => contradiction
        | inr hc => exact hc
        exact Or.inr ⟨ha, hc⟩
    · intro h
      cases h with
      | inl hab => exact ⟨hab.left, Or.inl hab.right⟩
      | inr hac => exact ⟨hac.left, Or.inr hac.right⟩
  · intro A B C
    funext x
    simp
    constructor
    · intro ⟨hab, hc⟩
      cases hab with
      | inl ha => exact Or.inl ⟨ha, hc⟩
      | inr hb => exact Or.inr ⟨hb, hc⟩
    · intro h
      cases h with
      | inl hac => exact ⟨Or.inl hac.left, hac.right⟩
      | inr hbc => exact ⟨Or.inr hbc.left, hbc.right⟩

def Set.image (f: α → β) (A: Set α): Set β :=
  λ b ↦ ∃ a ∈ A, f a = b

def Set.preimage (f: α → β) (B: Set β): Set α :=
  λ a ↦ f a ∈ B

def Set.range (f: α → β): Set β :=
  λ b ↦ ∃ a, f a = b
