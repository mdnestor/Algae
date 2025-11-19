class ExistsUnique {X: Type u} (P: X → Prop): Prop where
  exist: ∃ x, P x
  unique: ∀ x y, P x → P y → x = y

theorem contrapose {P Q: Prop}: (¬Q → ¬P) → (P → Q) := by
  intro h hP
  by_cases hQ: Q
  · exact hQ
  · have := h hQ
    contradiction

theorem contrapose_iff {P Q: Prop}: (¬Q ↔ ¬P) → (P ↔ Q) := by
  intro ⟨h1, h2⟩
  constructor
  · apply contrapose
    exact h1
  · apply contrapose
    exact h2
