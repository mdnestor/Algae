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



-- Definition of a (left) action of a monoid α on a set X.

class Action (α: Type v) [Monoid α] (X: Type u) where
  act: α → X → X
  op: ∀ a b x, act a (act b x) = act (a + b) x
  id: ∀ x, act 0 x = x



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



-- Every monoid acts on itself via its operation.

def Action.endo (M: Monoid α): Action α α := {
  act := M.op
  op := by
    intro a b c
    calc
      a + (b + c)
      _ = a + b + c := by rw [op_assoc]
  id := by exact op_unit_left
}

-- Every action of α on X corresponds to homomorphism from α^op to the monoid of endofunctions on X.
-- (Note we need to take α^op since we use left actions.)

def Monoid.endoaction [M: Monoid α] [A: Action α X]: hom M.opposite (Monoid.endo X) := {
  map := act
  unit_preserving := by
    ext x
    exact act_id x
  op_preserving := by
    intro a b
    ext x
    calc
      (b + a) • x
        = b • (a • x) := by rw [act_op]
      _ = op (act a) (act b) x := by rfl
}



-- The reachability relation induced by an action:
-- x relates to y if there exists a ∈ α such that acting via a on x yields y.
-- An action is transitive if every element is reachable from every other element.

def Action.reachable [Monoid α] (A: Action α X): Endorelation X :=
  λ x y ↦ ∃ a: α, a • x = y

def Action.transitive [Monoid α] (A: Action α X): Prop :=
  ∀ x y, A.reachable x y

-- The reachability relation is reflexive and transitive, hence a preorder.

theorem Action.reachable_reflexive [Monoid α] (A: Action α X): Reflexive A.reachable := by
  intro x
  exists 0
  exact act_id x

theorem Action.reachable_transitive [Monoid α] (A: Action α X): Transitive A.reachable := by
  intro x y z ⟨a, ha⟩ ⟨b, hb⟩
  exists b + a
  rw [←act_op, ha, hb]

-- The reachability relation induced by a group action is symmetric, and hence an equivalence.

theorem Action.reachable_symmetric [Group α] (A: Action α X): Symmetric A.reachable := by
  intro x y ⟨a, ha⟩
  exists -a
  exact act_inv ha

theorem Action.reachable_equivalence [Group α] (A: Action α X): Equivalence A.reachable := by
  exact ⟨A.reachable_reflexive, A.reachable_symmetric, A.reachable_transitive⟩

def Action.quotient [Group α] (A: Action α X): Type v :=
  Quotient ⟨A.reachable, A.reachable_equivalence⟩



-- Faithful/free/regular actions.

def Action.faithful [Monoid α] (A: Action α X): Prop :=
  ∀ a: α, (∀ x: X, a • x = x) → a = 0

def Action.free [Monoid α] (A: Action α X): Prop :=
  ∀ a: α, (∃ x: X, a • x = x) → a = 0

theorem Action.free_implies_faithful [Nonempty X] [Monoid α] (A: Action α X) (h: A.free): A.faithful := by
  intro a ha
  apply h a
  exists Classical.ofNonempty
  exact ha Classical.ofNonempty

def Action.regular [Monoid α] (A: Action α X): Prop :=
  A.free ∧ A.transitive

theorem Action.regular_iff [Monoid α] (A: Action α X): A.regular ↔ ∀ x y, ExistsUnique (λ a ↦ A.act a x = y) := by
  sorry



-- TODO: show the action of the symmetric group is transitive

-- TODO: show every group action corresponds to a group homomorphism to the symmetric group on X.



-- The orbit of x wrt. an action is the set of points reachable from x.

def Action.orbit [Monoid α] (A: Action α X) (x: X): Set X :=
  λ y ↦ A.reachable x y

-- An action is transitive iff. the orbit of every point is the whole set.

theorem action_transitive_iff_orbit_full [Group α] {A: Action α X}: A.transitive ↔ ∀ x, A.orbit x = Set.full := by
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



-- The stabilizer x is the set of a ∈ α that fix x.

def Stabilizer [Monoid α] (A: Action α X) (x: X): Set α :=
  λ a ↦ a • x = x

-- The monoid unit is always in the stabilizer.

theorem stabilizer_unit_mem [Monoid α] (A: Action α X) (x: X): unit ∈ Stabilizer A x := by
  exact act_id x

-- The stabilizer of a monoid/group action is a submonoid/subgroup respectively..

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

-- An action is free iff. all its stabilizers are singletons.

theorem Action.free_iff_all_stabilizers_trivial [Group α] {A: Action α X}: A.free ↔ ∀ x, Stabilizer A x = Set.singleton unit := by
  sorry



-- An invariant set is closed under the action.

def Action.invariant_set [Monoid α] (A: Action α X) (S: Set X): Prop :=
  ∀ a x, x ∈ S → A.act a x ∈ S
