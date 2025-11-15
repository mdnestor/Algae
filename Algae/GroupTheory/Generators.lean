import Algae.GroupTheory.Group

variable {α: Type u}

open Group

def nmul_range [Monoid α] (a: α): Set α :=
  Set.range (λ n: Nat ↦ n • a)

theorem ngen_submonoid [M: Monoid α] (a: α): M.sub (nmul_range a) := {
  unit_mem := by exists 0
  op_closed := by
    intro x y ⟨n, hn⟩ ⟨m, hm⟩
    exists (n + m)
    simp [←hn, ←hm, ngen_add]
}

def zmul_range [Group α] (a: α): Set α :=
  Set.range (λ n: Int ↦ n • a)

theorem ngen_subset_zgen [Group α] (a: α): nmul_range a ⊆ zmul_range a := by
  intro x ⟨n, hn⟩
  exists n

theorem zgen_subgroup [G: Group α] (a: α): G.sub (zmul_range a) := {
  unit_mem := by
    apply ngen_subset_zgen
    exact (ngen_submonoid a).unit_mem
  op_closed := by
    intro x y ⟨n, hn⟩ ⟨m, hm⟩
    exists (n  + m)
    simp [←hn, ← hm, zgen_add]
  inv_closed := by
    intro x ⟨n, hn⟩
    exists -n
    sorry
}

def Monoid.cyclic (M: Monoid α): Prop :=
  ∃ a, nmul_range a = @Set.full α

def Group.cyclic (G: Group α): Prop :=
  ∃ a, nmul_range a = @Set.full α

-- TODO: show Nat and Int are cyclic.
