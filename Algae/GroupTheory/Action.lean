/-

Actions, orbits, stabilizers.

TODO:
- orbit stabilizer theorem
hahah
-/

import Algae.GroupTheory.Group
import Algae.SetTheory.Relation
import Algae.SetTheory.Logic

variable {α: Type u} {X: Type v}

class Action (α: Type u) [Monoid α] (X: Type v) where
  act: α → X → X
  act_op: ∀ a b x, act (op a b) x = act b (act a x)
  act_id: LeftIdentity act unit

export Action (act)

instance [Monoid α] [Action α X]: SMul α X := {
  smul := Action.act
}

theorem act_inv [Group α] [Action α X] {a: α} {x y: X} (h: act a x = y) : act (inv a) y = x := by
  rw [←h, ←Action.act_op, Group.inverse.right, Action.act_id]

-- Every monoid defines an action on itself.
def Action.endo (M: Monoid α): Action α α := {
  act := flip op
  act_op := by
    intro a b c
    simp [flip]
    to_additive
    rw [op_assoc]
  act_id := Monoid.identity.right
}

def Action.faithful [Monoid α] (A: Action α X): Prop :=
  ∀ a, (∀ x, A.act a x = x) → a = unit

def Action.free [Monoid α] (A: Action α X): Prop :=
  ∀ a, (∃ x, A.act a x = x) → a = unit

theorem free_implies_faithful [Nonempty X] [Monoid α] {A: Action α X} (h: A.free): A.faithful := by
  intro a ha
  apply h a
  exists Classical.ofNonempty
  exact ha Classical.ofNonempty

-- The orbit of an point under an action.
def Action.orbit [Monoid α] (A: Action α X) (x: X): Set X :=
  λ y ↦ ∃ a, A.act a x = y

-- The reachability relation induced by an action.
def Action.reachable [Monoid α] (A: Action α X): Endorelation X :=
  λ x y ↦ y ∈ A.orbit x

theorem Action.reachable_reflexive [Monoid α] (A: Action α X): Reflexive A.reachable := by
  intro x
  exists unit
  exact A.act_id x

theorem Action.reachable_transitive [Monoid α] (A: Action α X): Transitive A.reachable := by
  intro x y z ⟨a, ha⟩ ⟨b, hb⟩
  exists op a b
  rw [A.act_op, ha, hb]

theorem Action.reachable_symmetric [Group α] (A: Action α X): Symmetric A.reachable := by
  intro x y ⟨a, ha⟩
  exists inv a
  exact act_inv ha

theorem Action.reachable_equivalence [Group α] (A: Action α X): Equivalence A.reachable := by
  exact ⟨A.reachable_reflexive, A.reachable_symmetric, A.reachable_transitive⟩

def Action.quotient [Group α] (A: Action α X): Type v :=
  Quotient ⟨A.reachable, A.reachable_equivalence⟩

def Action.transitive [Monoid α] (A: Action α X): Prop :=
  ∀ x y, A.reachable x y

def Action.regular [Monoid α] (A: Action α X): Prop :=
  A.free ∧ A.transitive

theorem Action.regular_iff [Monoid α] (A: Action α X): A.regular ↔ ∀ x y, ExistsUnique (λ a ↦ A.act a x = y) := by
  sorry

-- TODO: show the action of the symmetric group is transitive

-- Every action of α on X corresponds to homomorphism from α to the monoid of endofunctions on X.
example [Monoid α] (A: Action α X): MonoidHom A.act := {
  unit_preserving := by
    ext x
    exact A.act_id x
  op_preserving := by
    intro a b
    ext x
    calc
      act (op a b) x
      _ = act b (act a x) := by rw [A.act_op]
      _ = op (act a) (act b) x := by rfl
}

-- TODO: show every group action corresponds to a group homomorphism to the symmetric group on X.

def Orbit [Monoid α] (A: Action α X) (x: X): Set X :=
  λ y ↦ A.reachable x y

theorem orbit_eq_cofiber [Monoid α] (A: Action α X) (x: X): Orbit A x = A.reachable.cofiber x := by
  rfl

theorem orbit_basepoint_mem [Monoid α] {A: Action α X} (x: X): x ∈ Orbit A x := by
  exists unit
  apply A.act_id

theorem orbit_symmetric [Group α] {A: Action α X} {x y: X} (h: y ∈ Orbit A x): x ∈ Orbit A y := by
  obtain ⟨a, ha⟩ := h
  exists inv a
  exact act_inv ha

theorem orbit_transitive [Group α] {A: Action α X} {x y z: X} (h₁: y ∈ Orbit A x) (h₂: z ∈ Orbit A y): z ∈ Orbit A x := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exists op a b
  rw [A.act_op, ha, hb]

theorem action_transitive_iff_orbit_full [Group α] {A: Action α X}: A.transitive ↔ ∀ x, A.orbit x = Set.full X := by
  constructor
  · intro h x
    funext y
    apply propext
    constructor
    · intro; trivial
    · intro; exact h x y
  · intro h x y
    have hx := h x
    have: y ∈ Set.full X := trivial
    rw [←hx] at this
    exact this

-- Theorem: For a group action, if x ∈ orbit(x0) then orbit(x) = orbit(x0)
theorem orbit_mem_orbit_eq [Group α] (A: Action α X) (x₀ x) (h: x ∈ Orbit A x₀): Orbit A x = Orbit A x₀ := by
  obtain ⟨a, ha⟩ := h
  funext y
  apply propext
  constructor
  · intro ⟨b, hb⟩
    exists op a b
    rw [A.act_op, ha, hb]
  · intro ⟨b, hb⟩
    exists op (inv a) b
    rw [A.act_op, act_inv ha, hb]



-- Given an action of M on X, the stabilizer of x is the set of a in M which fix x.
def Stabilizer [Monoid α] (A: Action α X) (x: X): Set α :=
  λ a ↦ act a x = x

theorem stabilizer_unit_mem [Monoid α] (A: Action α X) (x: X): unit ∈ Stabilizer A x := by
  exact A.act_id x

theorem Stabilizer.submonoid [Monoid α] (A: Action α X) (x: X): Submonoid (Stabilizer A x) := {
  unit_mem := stabilizer_unit_mem A x
  op_closed := by
    intro a b ha hb
    calc
      act (op a b) x
      _ = act b (act a x) := by rw [Action.act_op]
      _ = act b x := by rw [ha]
      _ = x := by rw [hb]
}

theorem Stabilizer.subgroup [Group α] (A: Action α X) (x: X): Subgroup (Stabilizer A x) := {
  unit_mem := (Stabilizer.submonoid _ _).unit_mem
  op_closed := (Stabilizer.submonoid _ _).op_closed
  inv_closed := by intro; exact act_inv
}

theorem Action.free_iff_all_stabilizers_trivial [Group α] {A: Action α X}: A.free ↔ ∀ x, Stabilizer A x = Set.singleton unit := by
  sorry

def Action.invariant_set [Monoid α] (A: Action α X) (S: Set X): Prop :=
  ∀ a x, x ∈ S → A.act a x ∈ S
