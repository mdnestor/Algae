import Algae.GroupTheory.Group
import Algae.SetTheory.Relation
import Algae.SetTheory.Logic
open Group

/-

Actions, orbits, stabilizers.

TODO:
- refactor action to reference acting object explicitly?
- orbit stabilizer theorem

-/

class Action (α: Type v) [Monoid α] (X: Type u) where
  act: α → X → X
  op: ∀ a b x, act a (act b x) = act (a + b) x
  id: LeftIdentity act 0



export Action (act)
variable {α: Type u} {X: Type v}
instance [Monoid α] [Action α X]: SMul α X := ⟨Action.act⟩



theorem act_op [Monoid α] [Action α X] (x: X) (a b: α): a • (b • x) = (a + b) • x := by
  apply Action.op

theorem act_id [Monoid α] [Action α X] (x: X): (0: α) • x = x := by
  apply Action.id

theorem act_inv [Group α] [Action α X] {a: α} {x z: X} (h: a • x = z): -a • z = x := by
  calc
    -a • z
      = -a • (a • x) := by rw [←h]
    _ = (-a + a) • x := by rw [act_op]
    _ = (0: α) • x := by rw [op_inv_left]
    _ = x := by rw [act_id]

-- Every monoid defines an action on itself.
def Action.endo (M: Monoid α): Action α α := {
  act := M.op
  op := by
    intro a b c
    calc
      a + (b + c)
      _ = a + b + c := by rw [op_assoc]
  id := by exact op_unit_left
}



def Action.faithful [Monoid α] (A: Action α X): Prop :=
  ∀ a: α, (∀ x: X, a • x = x) → a = 0

def Action.free [Monoid α] (A: Action α X): Prop :=
  ∀ a: α, (∃ x: X, a • x = x) → a = 0

theorem Action.free_implies_faithful [Nonempty X] [Monoid α] (A: Action α X) (h: A.free): A.faithful := by
  intro a ha
  apply h a
  exists Classical.ofNonempty
  exact ha Classical.ofNonempty



-- The orbit of an point under an action.
def Action.orbit [Monoid α] (A: Action α X) (x: X): Set X :=
  λ y ↦ ∃ a: α, a • x = y

-- The reachability relation induced by an action.
def Action.reachable [Monoid α] (A: Action α X): Endorelation X :=
  λ x y ↦ x ∈ A.orbit y

theorem Action.reachable_reflexive [Monoid α] (A: Action α X): Reflexive A.reachable := by
  intro x
  exists 0
  exact act_id x

theorem Action.reachable_transitive [Monoid α] (A: Action α X): Transitive A.reachable := by
  intro x y z ⟨a, ha⟩ ⟨b, hb⟩
  exists a + b
  rw [←act_op, hb, ha]

theorem Action.reachable_symmetric [Group α] (A: Action α X): Symmetric A.reachable := by
  intro x y ⟨a, ha⟩
  exists -a
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
def Monoid.endoaction [M: Monoid α] [A: Action α X]: hom M (Monoid.endo X).opposite := {
  map := act
  unit_preserving := by
    ext x
    exact act_id x
  op_preserving := by
    intro a b
    ext x
    calc
      (a + b) • x
        = a • (b • x) := by rw [act_op]
      _ = op (act b) (act a) x := by rfl
}

-- TODO: show every group action corresponds to a group homomorphism to the symmetric group on X.

def Orbit [Monoid α] (A: Action α X) (x: X): Set X :=
  λ y ↦ A.reachable x y

theorem orbit_eq_cofiber [Monoid α] (A: Action α X) (x: X): Orbit A x = A.reachable.cofiber x := by
  rfl

theorem orbit_basepoint_mem [Monoid α] {A: Action α X} (x: X): x ∈ Orbit A x := by
  exists unit
  apply act_id

theorem orbit_symmetric [Group α] {A: Action α X} {x y: X} (h: y ∈ Orbit A x): x ∈ Orbit A y := by
  obtain ⟨a, ha⟩ := h
  exists inv a
  exact act_inv ha

theorem orbit_transitive [Group α] {A: Action α X} {x y z: X} (h₁: y ∈ Orbit A x) (h₂: z ∈ Orbit A y): z ∈ Orbit A x := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exists a + b
  rw [←act_op, hb, ha]

theorem action_transitive_iff_orbit_full [Group α] {A: Action α X}: A.transitive ↔ ∀ x, A.orbit x = Set.full := by
  constructor
  · intro h x
    funext y
    apply propext
    constructor
    · intro; trivial
    · intro; exact h y x
  · intro h x y
    have hy := h y
    have: x ∈ Set.full := trivial
    rw [←hy] at this
    exact this

-- Theorem: For a group action, if x ∈ orbit(x0) then orbit(x) = orbit(x0)
theorem orbit_mem_orbit_eq [Group α] {A: Action α X} {x₀ x: X} (h: x ∈ Orbit A x₀): Orbit A x = Orbit A x₀ := by
  obtain ⟨a, ha⟩ := h
  funext y
  apply propext
  constructor
  · intro ⟨b, hb⟩
    exists a + b
    rw [←act_op, hb, ha]
  · intro ⟨b, hb⟩
    exists -a + b
    rw [←act_op, hb, act_inv ha]



-- Given an action of M on X, the stabilizer of x is the set of a in M which fix x.
def Stabilizer [Monoid α] (A: Action α X) (x: X): Set α :=
  λ a ↦ a • x = x

theorem stabilizer_unit_mem [Monoid α] (A: Action α X) (x: X): unit ∈ Stabilizer A x := by
  exact act_id x

theorem Stabilizer.submonoid [M: Monoid α] (A: Action α X) (x: X): M.sub (Stabilizer A x) := {
  unit_mem := stabilizer_unit_mem A x
  op_closed := by
    intro a b ha hb
    calc
      (a + b) • x
       = a • (b • x) := by rw [act_op]
      _ = a • x := by rw [hb]
      _ = x := by rw [ha]
}

theorem Stabilizer.subgroup [G: Group α] (A: Action α X) (x: X): Group.sub G (Stabilizer A x) := {
  unit_mem := (Stabilizer.submonoid _ _).unit_mem
  op_closed := (Stabilizer.submonoid _ _).op_closed
  inv_closed := by intro; exact act_inv
}

theorem Action.free_iff_all_stabilizers_trivial [Group α] {A: Action α X}: A.free ↔ ∀ x, Stabilizer A x = Set.singleton unit := by
  sorry

def Action.invariant_set [Monoid α] (A: Action α X) (S: Set X): Prop :=
  ∀ a x, x ∈ S → A.act a x ∈ S
