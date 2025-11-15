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

class Action (X: Type u) (α: Type v) [Monoid α] where
  act: α → X → X
  op: ∀ a b x, act b (act a x) = act (a + b) x
  id: LeftIdentity act 0



export Action (act)
variable {α: Type u} {X: Type v}
instance [Monoid α] [Action X α]: HSMul X α X := ⟨flip Action.act⟩



theorem act_op [Monoid α] [Action X α] (x: X) (a b: α): (x • a) • b = x • (a + b) := by
  apply Action.op

theorem act_id [Monoid α] [Action X α] (x: X): x • (0: α) = x := by
  apply Action.id

theorem act_inv [Group α] [Action X α] {a: α} {x z: X} (h: x • a = z): z • -a = x := by
  calc
    z • -a
      = (x • a) • -a := by rw [←h]
    _ = x • (a + -a) := by rw [act_op]
    _ = x • (0: α) := by rw [op_inv_right]
    _ = x := by rw [act_id]

-- Every monoid defines an action on itself.
def Action.endo (M: Monoid α): Action α α := {
  act := flip M.op
  op := by
    intro a b c
    calc
      (c + a) + b
      _ = c + (a + b) := by rw [op_assoc]
  id := by exact op_unit_right
}



def Action.faithful [Monoid α] (A: Action X α): Prop :=
  ∀ a: α, (∀ x: X, x • a = x) → a = 0

def Action.free [Monoid α] (A: Action X α): Prop :=
  ∀ a: α, (∃ x: X, x • a = x) → a = 0

theorem Action.free_implies_faithful [Nonempty X] [Monoid α] (A: Action X α) (h: A.free): A.faithful := by
  intro a ha
  apply h a
  exists Classical.ofNonempty
  exact ha Classical.ofNonempty



-- The orbit of an point under an action.
def Action.orbit [Monoid α] (A: Action X α) (x: X): Set X :=
  λ y ↦ ∃ a: α, x • a = y

-- The reachability relation induced by an action.
def Action.reachable [Monoid α] (A: Action X α): Endorelation X :=
  λ x y ↦ y ∈ A.orbit x

theorem Action.reachable_reflexive [Monoid α] (A: Action X α): Reflexive A.reachable := by
  intro x
  exists 0
  exact act_id x

theorem Action.reachable_transitive [Monoid α] (A: Action X α): Transitive A.reachable := by
  intro x y z ⟨a, ha⟩ ⟨b, hb⟩
  exists a + b
  rw [←act_op, ha, hb]

theorem Action.reachable_symmetric [Group α] (A: Action X α): Symmetric A.reachable := by
  intro x y ⟨a, ha⟩
  exists -a
  exact act_inv ha

theorem Action.reachable_equivalence [Group α] (A: Action X α): Equivalence A.reachable := by
  exact ⟨A.reachable_reflexive, A.reachable_symmetric, A.reachable_transitive⟩

def Action.quotient [Group α] (A: Action X α): Type v :=
  Quotient ⟨A.reachable, A.reachable_equivalence⟩

def Action.transitive [Monoid α] (A: Action X α): Prop :=
  ∀ x y, A.reachable x y

def Action.regular [Monoid α] (A: Action X α): Prop :=
  A.free ∧ A.transitive

theorem Action.regular_iff [Monoid α] (A: Action X α): A.regular ↔ ∀ x y, ExistsUnique (λ a ↦ A.act a x = y) := by
  sorry

-- TODO: show the action of the symmetric group is transitive

-- Every action of α on X corresponds to homomorphism from α to the monoid of endofunctions on X.
def Monoid.endoaction [M: Monoid α] [A: Action X α]: hom M (Monoid.endo X) := {
  map := act
  unit_preserving := by
    ext x
    exact act_id x
  op_preserving := by
    intro a b
    ext x
    calc
      x • (a + b)
        = (x • a) • b := by rw [act_op]
      _ = op (act a) (act b) x := by rfl
}

-- TODO: show every group action corresponds to a group homomorphism to the symmetric group on X.

def Orbit [Monoid α] (A: Action X α) (x: X): Set X :=
  λ y ↦ A.reachable x y

theorem orbit_eq_cofiber [Monoid α] (A: Action X α) (x: X): Orbit A x = A.reachable.cofiber x := by
  rfl

theorem orbit_basepoint_mem [Monoid α] {A: Action X α} (x: X): x ∈ Orbit A x := by
  exists unit
  apply act_id

theorem orbit_symmetric [Group α] {A: Action X α} {x y: X} (h: y ∈ Orbit A x): x ∈ Orbit A y := by
  obtain ⟨a, ha⟩ := h
  exists inv a
  exact act_inv ha

theorem orbit_transitive [Group α] {A: Action X α} {x y z: X} (h₁: y ∈ Orbit A x) (h₂: z ∈ Orbit A y): z ∈ Orbit A x := by
  obtain ⟨a, ha⟩ := h₁
  obtain ⟨b, hb⟩ := h₂
  exists a + b
  rw [←act_op, ha, hb]

theorem action_transitive_iff_orbit_full [Group α] {A: Action X α}: A.transitive ↔ ∀ x, A.orbit x = Set.full := by
  constructor
  · intro h x
    funext y
    apply propext
    constructor
    · intro; trivial
    · intro; exact h x y
  · intro h x y
    have hx := h x
    have: y ∈ Set.full := trivial
    rw [←hx] at this
    exact this

-- Theorem: For a group action, if x ∈ orbit(x0) then orbit(x) = orbit(x0)
theorem orbit_mem_orbit_eq [Group α] {A: Action X α} {x₀ x: X} (h: x ∈ Orbit A x₀): Orbit A x = Orbit A x₀ := by
  obtain ⟨a, ha⟩ := h
  funext y
  apply propext
  constructor
  · intro ⟨b, hb⟩
    exists a + b
    rw [←act_op, ha, hb]
  · intro ⟨b, hb⟩
    exists -a + b
    rw [←act_op, act_inv ha, hb]



-- Given an action of M on X, the stabilizer of x is the set of a in M which fix x.
def Stabilizer [Monoid α] (A: Action X α) (x: X): Set α :=
  λ a ↦ x • a = x

theorem stabilizer_unit_mem [Monoid α] (A: Action X α) (x: X): unit ∈ Stabilizer A x := by
  exact act_id x

theorem Stabilizer.submonoid [M: Monoid α] (A: Action X α) (x: X): M.sub (Stabilizer A x) := {
  unit_mem := stabilizer_unit_mem A x
  op_closed := by
    intro a b ha hb
    calc
      x • (a + b)
       = (x • a) • b := by rw [act_op]
      _ = x • b := by rw [ha]
      _ = x := by rw [hb]
}

theorem Stabilizer.subgroup [G: Group α] (A: Action X α) (x: X): Group.sub G (Stabilizer A x) := {
  unit_mem := (Stabilizer.submonoid _ _).unit_mem
  op_closed := (Stabilizer.submonoid _ _).op_closed
  inv_closed := by intro; exact act_inv
}

theorem Action.free_iff_all_stabilizers_trivial [Group α] {A: Action X α}: A.free ↔ ∀ x, Stabilizer A x = Set.singleton unit := by
  sorry

def Action.invariant_set [Monoid α] (A: Action X α) (S: Set X): Prop :=
  ∀ a x, x ∈ S → A.act a x ∈ S
