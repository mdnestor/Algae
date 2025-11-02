import Algae.Basic

variable {α: Type u} {β: Type v}

def Function.id {α: Type u}: α → α :=
  λ a ↦ a

def Function.constant (α: Type u) {β: Type v} (b: β): α → β :=
  λ _ ↦ b

def Function.Bijective  (f: α → β): Prop :=
  Injective f ∧ Surjective f

def Function.inverses (f: α → β) (g: β → α): Prop :=
  g ∘ f = id

theorem Function.inverses_id: inverses (@id α) (@id α) := by
  constructor <;> rfl

theorem Function.inverses_comp (hf: inverses f f') (hg: inverses g g'): inverses (g ∘ f) (f' ∘ g') := by
  calc
    (f' ∘ g') ∘ g ∘ f
  _ = f' ∘ (g' ∘ g) ∘ f := by rfl
  _ = f' ∘ id ∘ f := by rw [hg]
  _ = f' ∘ f := by rfl
  _ = id := by rw [hf]

def Function.invertible (f: α → β): Prop :=
  ∃ g, Function.inverses f g ∧ Function.inverses g f

theorem Function.invertible_id {α: Type u}: Function.invertible (@id α) := by
  exists id

theorem Function.invertible_comp {f: α → β} {g: β → γ} (hf: invertible f) (hg: invertible g): invertible (g ∘ f) := by
  obtain ⟨f', hf⟩ := hf
  obtain ⟨g', hg⟩ := hg
  exists f' ∘ g'
  constructor
  exact Function.inverses_comp hf.left hg.left
  exact Function.inverses_comp hg.right hf.right

def Function.associator (A: Type u) (B: Type v) (C: Type w): A × B × C → (A × B) × C :=
  λ ⟨a, ⟨b, c⟩⟩ ↦ ⟨⟨a, b⟩, c⟩

def Function.associator_inverse (A: Type u) (B: Type v) (C: Type w): (A × B) × C → A × B × C :=
  λ ⟨⟨a, b⟩, c⟩ ↦ ⟨a, ⟨b, c⟩⟩


def Set (α: Type u): Type u :=
  α → Prop

instance (α: Type u): CoeSort (Set α) (Type u) := {
  coe := Subtype
}

def Set.empty (α: Type u): Set α :=
  λ _ ↦ False

def Set.full (α: Type u): Set α :=
  λ _ ↦ True

-- define this
def Set.singleton {α: Type u} (a: α): Set α :=
  λ x ↦ x = a

instance: Membership α (Set α) := {
  mem := λ A a ↦ A a
}

instance: HasSubset (Set α) := {
  Subset := λ A B ↦ ∀ x, A x → B x
}

instance: EmptyCollection (Set α) := {
  emptyCollection := Set.empty α
}

theorem Set.empty_subset (A: Set α): ∅ ⊆ A := by
  exact fun _ => False.elim

theorem Set.subset_full (A: Set α): A ⊆ Set.full α := by
  exact fun _ _ => trivial

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
  union := Set.inter
}

theorem Set.union_left {A B: Set α} {a: α} (h: a ∈ A): a ∈ A ∪ B := by
  sorry

theorem Set.union_right {A B: Set α} {a: α} (h: a ∈ B): a ∈ A ∪ B := by
  sorry

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

theorem Set.inter_identity: Identity Set.inter (Set.full α) := by
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

def Set.iUnion (A: ι → Set α): Set α :=
  λ a ↦ ∃ i, a ∈ A i

def Set.iInter (A: ι → Set α): Set α :=
  λ a ↦ ∀ i, a ∈ A i

class ExistsUnique {X: Type u} (P: X → Prop): Prop where
  exist: ∃ x, P x
  unique: ∀ x y, P x → P y → x = y
