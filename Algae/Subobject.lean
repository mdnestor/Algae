import Algae.Group

variable {α: Type u}

class Submagma [Magma α] (S: Set α): Prop where
  op_closed: ∀ a b, a ∈ S → b ∈ S → op a b ∈ S

class Subpointed [Pointed α] (S: Set α): Prop where
  unit_mem: unit ∈ S

class Submonoid [Monoid α] (S: Set α) extends Submagma S, Subpointed S

class Subgroup [Group α] (S: Set α) extends Submonoid S where
  inv_closed: ∀ a, a ∈ S → inv a ∈ S

def Submonoid.toMonoid [Monoid α] (S: Set α) (h: Submonoid S): Monoid S :=
  sorry

def nmul_generate [Monoid α] (a: α): Set α :=
  Set.range (λ n: Nat ↦ n • a)

theorem nmul_generate_submonoid [Monoid α] (a: α): Submonoid (nmul_generate a) := {
  unit_mem := by
    exists 0
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
    simp [←hn, ←neg_eq, ←zmul_neg', zmul_neg]
}
