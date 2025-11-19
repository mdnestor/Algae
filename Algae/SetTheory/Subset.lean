import Algae.SetTheory.Operation
import Algae.SetTheory.Logic

variable {α: Type u} {β: Type v} {γ: Type w}

def Set (α: Type u): Type u :=
  α → Prop

instance (α: Type u): CoeSort (Set α) (Type u) := {
  coe := Subtype
}

def Set.empty {α: Type u}: Set α :=
  λ _ ↦ False

def Set.full {α: Type u}: Set α :=
  λ _ ↦ True

def Set.singleton {α: Type u} (a: α): Set α :=
  λ x ↦ x = a

instance: Membership α (Set α) := {
  mem := λ A a ↦ A a
}

instance: HasSubset (Set α) := {
  Subset := λ A B ↦ ∀ x, A x → B x
}

instance: EmptyCollection (Set α) := {
  emptyCollection := Set.empty
}

theorem Set.empty_subset (A: Set α): ∅ ⊆ A := by
  exact λ _ ↦ False.elim

theorem Set.subset_full (A: Set α): A ⊆ Set.full := by
  exact λ _ _ ↦ trivial

def Set.inter (A B: Set α): Set α :=
  λ x ↦ x ∈ A ∧ x ∈ B

instance: Inter (Set α) := {
  inter := Set.inter
}

theorem Set.inter_left {A B: Set α} {a: α} (h: a ∈ A ∩ B): a ∈ A := by
  exact h.left

theorem Set.inter_right {A B: Set α} {a: α} (h: a ∈ A ∩ B): a ∈ B := by
  exact h.right

def Set.union (A B: Set α): Set α :=
  λ x ↦ x ∈ A ∨ x ∈ B

instance: Union (Set α) := {
  union := Set.union
}

theorem Set.union_left {A B: Set α} {a: α} (h: a ∈ A): a ∈ A ∪ B := by
  apply Or.inl
  exact h

theorem Set.union_right {A B: Set α} {a: α} (h: a ∈ B): a ∈ A ∪ B := by
  apply Or.inr
  exact h

def Set.compl (A: Set α): Set α :=
  λ x ↦ x ∉ A

def Set.nonempty (S: Set α): Prop :=
  ∃ a, a ∈ S

theorem Set.nonempty_iff {S: Set α}: S.nonempty ↔ S ≠ ∅ := by
  constructor
  · intro ⟨a, ha⟩
    intro h
    have: a ∉ S := by exact of_eq_false (congrFun h a)
    contradiction
  · apply contrapose
    simp [Set.nonempty]
    intro h
    funext _
    simp
    constructor
    · intro h'
      exact h _ h'
    · intro h'
      exact False.elim h'

theorem Set.not_nonempty_iff {S: Set α}: ¬S.nonempty ↔ S = ∅ := by
  apply contrapose_iff
  simp
  exact Iff.symm nonempty_iff

theorem Set.compl_empty_iff {S: Set α}: S.compl = ∅ ↔ S = Set.full := by
  constructor
  · intro h
    funext x
    simp
    constructor
    · intro
      trivial
    · intro _
      by_cases hx: x ∈ S
      · exact hx
      · have: x ∈ S.compl := by exact hx
        simp_all
        contradiction
  · intro h
    funext x
    simp
    constructor
    · intro h'
      by_cases hx: x ∈ S
      · contradiction
      · rw [h] at hx
        have: x ∈ full := by trivial
        contradiction
    · intro h'
      contradiction

def Set.subtype (A: Set α): Type u :=
  Σ a, PLift (a ∈ A)

theorem Set.union_left_identity: LeftIdentity Set.union (@Set.empty α) := by
  intro
  funext
  simp [Set.union]
  exact or_iff_right id

theorem Set.union_right_identity: RightIdentity Set.union (@Set.empty α) := by
  intro
  funext
  simp [Set.union]
  exact or_iff_left id

theorem Set.union_identity: Identity Set.union (@Set.empty α) := by
  exact ⟨Set.union_left_identity, Set.union_right_identity⟩

theorem Set.union_assoc: Associative (@Set.union α) := by
  intro _ _ _
  funext
  simp [Set.union]
  constructor
  · intro h; cases h with
    | inl h => cases h with
      | inl => apply Or.inl; assumption
      | inr => apply Or.inr; apply Or.inl; assumption
    | inr => apply Or.inr; apply Or.inr; assumption
  · intro h; cases h with
    | inl => apply Or.inl; apply Or.inl; assumption
    | inr h => cases h with
      | inl => apply Or.inl; apply Or.inr; assumption
      | inr => apply Or.inr; assumption

theorem Set.union_comm: Commutative (@Set.union α) := by
  intro A B
  funext x
  simp [Set.union]
  exact Or.comm

theorem Set.inter_identity: Identity Set.inter (@Set.full α) := by
  constructor
  · intro
    funext
    simp [Set.inter]
    constructor
    · intro h; exact h.right
    · intro h; exact ⟨trivial, h⟩
  · intro
    funext
    simp [Set.inter]
    constructor
    · intro h; exact h.left
    · intro h; exact ⟨h, trivial⟩

def And.associative (P Q R: Prop): P ∧ Q ∧ R ↔ (P ∧ Q) ∧ R := by
  constructor
  intro ⟨p, q, r⟩
  exact ⟨⟨p, q⟩, r⟩
  intro ⟨⟨p, q⟩, r⟩
  exact ⟨p, q, r⟩

theorem Set.inter_assoc: Associative (@Set.inter α) := by
  intro _ _ _
  funext
  simp [Set.inter]
  apply Iff.symm
  apply And.associative

theorem Set.inter_comm: Commutative (@Set.inter α) := by
  intro A B
  funext x
  simp [Set.inter]
  constructor <;> (intro h; exact And.symm h;)

def Set.image (f: α → β) (A: Set α): Set β :=
  λ b ↦ ∃ a ∈ A, f a = b

def Set.preimage (f: α → β) (B: Set β): Set α :=
  λ a ↦ f a ∈ B

def Set.range (f: α → β): Set β :=
  λ b ↦ ∃ a, f a = b

theorem Set.range_mem (f: α → β) (a: α): f a ∈ Set.range f := by
  exists a

def Set.sUnion (S: Set (Set α)): Set α :=
  λ a ↦ ∃ A ∈ S, a ∈ A

theorem Set.sUnion_empty: Set.sUnion (∅: Set (Set α)) = ∅ := by
  funext x
  simp [Set.sUnion]
  constructor
  · intro ⟨_, _, _⟩
    contradiction
  · intro _
    contradiction

theorem Set.sUnion_full: Set.sUnion (Set.full: Set (Set α)) = Set.full := by
  funext x
  simp [Set.sUnion]
  constructor
  · intro ⟨_, ha₁, _⟩
    exact ha₁
  · intro _
    exists Set.singleton x

def Set.sInter (S: Set (Set α)): Set α :=
  λ a ↦ ∀ A ∈ S, a ∈ A

theorem Set.sInter_empty: Set.sInter (∅: Set (Set α)) = Set.full := by
  funext x
  simp [Set.sInter]
  constructor
  · intro _
    trivial
  · intro _ _ _
    contradiction

theorem Set.sInter_full: Set.sInter (Set.full: Set (Set α)) = ∅ := by
  funext x
  simp [Set.sInter]
  constructor
  · intro h
    have := h ∅ trivial
    contradiction
  · intro h
    contradiction
