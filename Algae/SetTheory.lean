import Algae.Basic

variable {α: Type u} {β: Type v}

def Function.id {α: Type u}: α → α :=
  λ x ↦ x

def Function.Bijective  (f: α → β): Prop :=
  Injective f ∧ Surjective f

def Set (α: Type u): Type u :=
  α → Prop

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
  intro h
  sorry
  sorry

theorem Set.union_comm: Commutative (@Set.union α) := by
  sorry

theorem Set.inter_identity: Identity Set.inter (Set.full α) := by
  sorry

theorem Set.inter_assoc: Associative (@Set.inter α) := by
  sorry

theorem Set.inter_comm: Commutative (@Set.inter α) := by
  sorry
-- you konw image? yeah

example: Distributive (@Set.union α) (@Set.inter α) := by
  sorry

example: Distributive (@Set.inter α) (@Set.union α) := by
  sorry

def Set.image (f: α → β) (A: Set α): Set β :=
  λ b ↦ ∃ a ∈ A, f a = b

def Set.preimage (f: α → β) (B: Set β): Set α :=
  λ a ↦ f a ∈ B

def Set.range (f: α → β): Set β :=
  λ b ↦ ∃ a, f a = b

-- ... im a little jokester.
-- ok yeah you are sleeping in the doghouse wha!! -- can you sleep there with me..'
-- sure yes! or we could just sleep inside in your bed :o
-- you might be covered in tire debris.. idk.. you never let me in your bed :(
-- i would give you a bath but i know you will shake and get the whole room wet..
-- bath unnecessary ?
--
-- joke definiton
