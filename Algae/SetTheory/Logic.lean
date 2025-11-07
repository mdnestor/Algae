class ExistsUnique {X: Type u} (P: X → Prop): Prop where
  exist: ∃ x, P x
  unique: ∀ x y, P x → P y → x = y
