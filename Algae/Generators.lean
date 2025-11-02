import Algae.Group

variable {α: Type u}

def nmul_generate [Monoid α] (a: α): Set α :=
  Set.range (λ n: Nat ↦ n • a)

theorem nmul_generate_submonoid [Monoid α] (a: α): Submonoid (nmul_generate a) := {
  unit_mem := by exists 0
  op_closed := by
    intro x y ⟨n, hn⟩ ⟨m, hm⟩
    exists (n + m)
    simp [←hn, ←hm, ←add_eq, nmul_add]
}

def zmul_generate [Group α] (a: α): Set α :=
  Set.range (λ n: Int ↦ n • a)

theorem nmul_generate_subset_zmul_generate [Group α] (a: α): nmul_generate a ⊆ zmul_generate a := by
  intro x ⟨n, hn⟩
  exists n

theorem zmul_generate_subgroup [Group α] (a: α): Subgroup (zmul_generate a) := {
  unit_mem := by
    apply nmul_generate_subset_zmul_generate
    exact (nmul_generate_submonoid a).unit_mem
  op_closed := by
    intro x y ⟨n, hn⟩ ⟨m, hm⟩
    exists (n  + m)
    simp [←hn, ← hm, ←add_eq, zmul_add]
  inv_closed := by
    intro x ⟨n, hn⟩
    exists -n
    sorry
    -- simp [←hn, ←neg_eq, ←zmul_neg', zmul_neg]
}

def Monoid.cyclic (M: Monoid α): Prop :=
  ∃ a, nmul_generate a = Set.full α

def Group.cyclic (G: Group α): Prop :=
  ∃ a, zmul_generate a = Set.full α

-- TODO: show Nat and Int are cyclic.
