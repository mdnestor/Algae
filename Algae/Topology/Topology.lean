import Algae.SetTheory.Finite

variable {X: Type u}

class Family (X: Type u) where
  Open: Set (Set X)

export Family (Open)

class Topology (X: Type u) extends Family X where
  UnionOpen: ∀ U ⊆ Open, U.sUnion ∈ Open
  InterOpen: ∀ U ⊆ Open, U.finite → U.sInter ∈ Open

theorem empty_open [Topology X]: Open (∅: Set X) := by
  rw [←Set.sUnion_empty]
  apply Topology.UnionOpen ∅
  apply Set.empty_subset

theorem full_open [Topology X]: Open (Set.full: Set X) := by
  rw [←Set.sInter_empty]
  apply Topology.UnionOpen ∅
  apply Set.empty_subset

theorem union_binary_open [Topology X] {A B: Set X} (hA: Open A) (hB: Open B): Open (A ∪ B) := by
  sorry

theorem inter_binary_open [Topology X] {A B: Set X} (hA: Open A) (hB: Open B): Open (A ∩ B) := by
  sorry



def Closed [Topology X] (A: Set X): Prop :=
  Open A.compl

def Clopen [Topology X] (A: Set X): Prop :=
  Open A ∧ Closed A

def Clopen't [Topology X] (A: Set X): Prop :=
  ¬Clopen A

def Separation [Topology X] (A: Set X): Prop :=
  Clopen A ∧ A.nonempty ∧ A.compl.nonempty

def Connected (X: Type u) [Topology X]: Prop :=
  ∀ A: Set X, ¬Separation A

theorem connected_iff [Topology X]: Connected X ↔ ∀ U: Set X, Clopen U → U = Set.full ∨ U = ∅ := by
  constructor
  · intro h U hU
    have := h U
    simp_all [Separation]
    by_cases h: U = ∅
    · exact Or.inr h
    · left
      have := this (Set.nonempty_iff.mpr h)
      have := Set.not_nonempty_iff.mp this
      exact Set.compl_empty_iff.mp this
  · intro h U
    simp [Separation]
    intro hU₁ hU₂
    have := h U hU₁
    simp_all [Set.nonempty_iff]
    exact Set.compl_empty_iff.mpr rfl


/-

TODO:
- Binary union/intersections are open
- Neighborhoods
- Interior/boundary/exterior
- Continuity
- Metric topology
- Metrizable space
- Separation axioms
- Metric → Hausdorff
- Metrizable → Hausdorff
- Nonhausdorff → Nonmetrizable

-/
