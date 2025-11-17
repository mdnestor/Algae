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

class Monoid.action {α: Type v} (M: Monoid α) (X: Type u) where
  act: α → X → X
  op: ∀ a b x, act a (act b x) = act (a + b) x
  id: ∀ x, act 0 x = x

instance [M: Monoid α] {X: Type u} (A: M.action X): CoeFun (M.action X) (λ _ ↦ α → X → X) := {
  coe _ := A.act
}

export Monoid.action (act)
variable {α: Type u} {X: Type v}
instance [M: Monoid α] [A: M.action X]: SMul α X := ⟨A.act⟩

-- An "opposite" action (i.e. a right action)

class Monoid.opaction (X: Type u) {α: Type v} (M: Monoid α) where
  act: α → X → X
  op: ∀ a b x, act a (act b x) = act (b + a) x
  id: ∀ x, act 0 x = x

def Monoid.opaction' (X: Type u) {α: Type v} (M: Monoid α): Type (max u v) :=
  M.opposite.action X

export Monoid.opaction (act)
variable {α: Type u} {X: Type v}
instance [M: Monoid α] [A: M.opaction X]: HSMul X α X := ⟨flip A.act⟩

-- An action of M on X corresponds to an op-action of M^op on X, and vice versa.

instance OpActiontoAction [M: Monoid α] [A: M.opaction X]: M.opposite.action X := {
  act := A.act
  op := A.op
  id := A.id
}

instance ActiontoOpAction [M: Monoid α] [A: M.action X]: M.opposite.opaction X := {
  act := A.act
  op := A.op
  id := A.id
}



theorem act_id [M: Monoid α] [M.action X] (x: X): (0: α) • x = x := by
  apply Monoid.action.id

theorem act_op [M: Monoid α] [M.action X] (x: X) (a b: α): a • (b • x) = (a + b) • x := by
  apply Monoid.action.op

theorem opact_op [M: Monoid α] [M.opaction X] (x: X) (a b: α): (x • a) • b = x • (a + b) := by
  apply Monoid.opaction.op

theorem act_inv [G: Group α] [G.action X] {a: α} {x z: X} (h: a • x = z): -a • z = x := by
  calc
    -a • z
      = -a • (a • x) := by rw [←h]
    _ = (-a + a) • x := by rw [act_op]
    _ = (0: α) • x := by rw [op_inv_left]
    _ = x := by rw [act_id]


-- Every monoid acts on itself via its operation.

def Monoid.self_action (M: Monoid α): M.action α := {
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

def Monoid.action.endo [M: Monoid α] (A: M.action X): hom M.opposite (Monoid.endo X) := {
  map := A.act
  unit_preserving := by
    ext x
    exact act_id x
  op_preserving := by
    intro a b
    ext x
    calc
      (b + a) • x
        = b • (a • x) := by rw [act_op]
      _ = (A.act a + A.act b) x := by rfl
}

-- Given a monoid action on X, there is an op-action X → Y defined (a • F)(x) = F(a • x), with

def Monoid.action.map_op {X: Type u} [M: Monoid α] (A: M.action X) (Y: Type v): M.opaction (X → Y) := {
  act := λ a f ↦ λ x ↦ f (a • x)
  op := by simp [act_op]
  id := by simp [act_id]
}

-- Given a group action on X, there is an action on X → Y defined (g • F)(x) = F(g⁻¹ • x).

def Monoid.action.map {X: Type u} [G: Group α] (A: G.action X) (Y: Type v): G.action (X → Y) := {
  act := λ a f ↦ λ x ↦ f (-a • x)
  op := by simp [inv_op, act_op]
  id := by simp [inv_unit, act_id]
}

-- When Y = Prop, we obtain actions of α on the powerset.

def Monoid.action.set_op {X: Type u} [M: Monoid α] (A: M.action X): M.opaction (Set X) :=
  Monoid.action.map_op A Prop

def Monoid.action.set {X: Type u} [G: Group α] (A: G.action X): G.action (Set X) :=
  Monoid.action.map A Prop



-- The reachability relation induced by an action:
-- x relates to y if there exists a ∈ α such that acting via a on x yields y.
-- An action is transitive if every element is reachable from every other element.

def Monoid.action.reachable [M: Monoid α] (A: M.action X): Endorelation X :=
  λ x y ↦ ∃ a: α, a • x = y

def Monoid.action.transitive [M: Monoid α] (A: M.action X): Prop :=
  ∀ x y, A.reachable x y

-- The reachability relation is reflexive and transitive, hence a preorder.

theorem Monoid.action.reachable_reflexive [M: Monoid α] (A: M.action X): Reflexive A.reachable := by
  intro x
  exists 0
  exact act_id x

theorem Monoid.action.reachable_transitive [M: Monoid α] (A: M.action X): Transitive A.reachable := by
  intro x y z ⟨a, ha⟩ ⟨b, hb⟩
  exists b + a
  rw [←act_op, ha, hb]

-- The reachability relation induced by a group action is symmetric, and hence an equivalence.

theorem Monoid.action.reachable_symmetric [G: Group α] (A: G.action X): Symmetric A.reachable := by
  intro x y ⟨a, ha⟩
  exists -a
  exact act_inv ha

theorem Monoid.action.reachable_equivalence [G: Group α] (A: G.action X): Equivalence A.reachable := by
  exact ⟨A.reachable_reflexive, A.reachable_symmetric, A.reachable_transitive⟩

def Monoid.action.orbits [G: Group α] (A: G.action X): Type v :=
  Quotient ⟨A.reachable, A.reachable_equivalence⟩



-- Faithful/free/regular actions.

def Monoid.action.faithful [M: Monoid α] (A: M.action X): Prop :=
  ∀ a: α, (∀ x: X, a • x = x) → a = 0

def Monoid.action.free [M: Monoid α] (A: M.action X): Prop :=
  ∀ a: α, (∃ x: X, a • x = x) → a = 0

theorem Monoid.action.free_implies_faithful [Nonempty X] [M: Monoid α] (A: M.action X) (h: A.free): A.faithful := by
  intro a ha
  apply h a
  exists Classical.ofNonempty
  exact ha Classical.ofNonempty

def Monoid.action.regular [M: Monoid α] (A: M.action X): Prop :=
  A.free ∧ A.transitive

theorem Monoid.action.regular_iff [M: Monoid α] (A: M.action X): A.regular ↔ ∀ x y, ExistsUnique (λ a ↦ A.act a x = y) := by
  sorry



-- TODO: show the action of the symmetric group is transitive

-- TODO: show every group action corresponds to a group homomorphism to the symmetric group on X.



-- The orbit of x wrt. an action is the set of points reachable from x.

def Monoid.action.orbit [M: Monoid α] (A: M.action X) (x: X): Set X :=
  λ y ↦ A.reachable x y

-- An action is transitive iff. the orbit of every point is the whole set.

theorem action_transitive_iff_orbit_full [G: Group α] {A: G.action X}: A.transitive ↔ ∀ x, A.orbit x = Set.full := by
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

def Stabilizer [M: Monoid α] (A: M.action X) (x: X): Set α :=
  λ a ↦ a • x = x

-- The monoid unit is always in the stabilizer.

theorem stabilizer_unit_mem [M: Monoid α] (A: M.action X) (x: X): unit ∈ Stabilizer A x := by
  exact act_id x

-- The stabilizer of a monoid/group action is a submonoid/subgroup respectively..

theorem Stabilizer.submonoid [M: Monoid α] (A: M.action X) (x: X): M.sub (Stabilizer A x) := {
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

theorem Monoid.action.free_iff_all_stabilizers_trivial [G: Group α] {A: G.action X}: A.free ↔ ∀ x, Stabilizer A x = Set.singleton unit := by
  sorry



-- An invariant set is closed under the action.

def Monoid.action.invariant_set [M: Monoid α] (A: M.action X) (S: Set X): Prop :=
  ∀ a x, x ∈ S → A.act a x ∈ S
