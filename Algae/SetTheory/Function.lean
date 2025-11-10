variable {α: Type u} {β: Type v} {γ: Type w}

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

def switch (f: α → β → γ): β → α → γ :=
  λ b a ↦ f a b

@[ext] structure InvertiblePair (α: Type u) (β: Type v) where
  map: α → β
  inv: β → α

@[ext] structure LeftInvertible (α: Type u) (β: Type v) extends InvertiblePair α β where
  id_left: inv ∘ map = id

@[ext] structure RightInvertible (α: Type u) (β: Type v) extends InvertiblePair α β where
  id_right: map ∘ inv = id

@[ext] structure Invertible (α: Type u) (β: Type v) extends LeftInvertible α β, RightInvertible α β

def Invertible.id {α: Type u}: Invertible α α := {
  map := Function.id
  inv := Function.id
  id_left := sorry
  id_right := sorry
}

def Invertible.inverse (f: Invertible α β): Invertible β α := {
  map := f.inv
  inv := f.map
  id_left := sorry
  id_right := sorry
}

def Invertible.comp (f: Invertible α β) (g: Invertible β γ): Invertible α γ := {
  map := g.map ∘ f.map
  inv := f.inv ∘ g.inv
  id_left := sorry
  id_right := sorry
}
