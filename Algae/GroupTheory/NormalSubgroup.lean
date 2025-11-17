import Algae.GroupTheory.Group
import Algae.GroupTheory.Action

variable {α: Type u}

open Group

-- The (left) conjugation by an element g ∈ G of a group is the map a ↦ gag⁻¹.
-- This is a left action of the group on itself.
-- (The map a ↦ g⁻¹ag is the right conjugation since it corresponds to a right action.)

def Conjugate [Group α] (g: α): α → α :=
  λ a ↦ g + a + -g

def Conjugate.action [Group α]: Action α α := {
  act := Conjugate
  id := by
    intro
    rw [Conjugate]
    rw [inv_unit, op_unit_left, op_unit_right]
  op := by
    intro a b x
    simp [Conjugate]
    apply Eq.symm
    calc
       ((a + b) + x) + -(a + b)
       _ = ((a + b) + x) + (-b + -a) := by rw [inv_op]
       _ = a + (b + x + -b) + -a := by simp [op_assoc]
}

-- A normal subgroup is one which is invariant under conjugation.

class Group.normalSubgroup [G: Group α] (S: Set α) extends toSubgroup: G.sub S where
  conj_invariant: Conjugate.action.invariant_set S

-- In a commutative group, conjugation is trivial since gag⁻¹ = agg⁻¹ = a.

theorem CommGroup.conjugate_trivial [CommGroup α] (g: α): Conjugate g = Function.id := by
  funext
  rw [Conjugate, op_comm, ←op_assoc, op_inv_left, op_unit_left, Function.id]

-- Thus in a commutative group, every subgroup is normal.

theorem CommGroup.subgroup_normal [G: CommGroup α] {S: Set α} (h: G.sub S): G.normalSubgroup S := by
  constructor
  intro _ _ hx
  simp [Conjugate.action, CommGroup.conjugate_trivial]
  exact hx



-- Given an element g and set S, the (left) coset is defined g + S = {g + a | a ∈ S}.
/-

Is `Coset` an action?
- 0 + S = S , true in a monoid
- a + (b + S) = (a + b) + S

LHS = {a + x | x ∈ b + S} = {a + x | x ∈ {b + y | y ∈ S}}
    = {a + (b + y) | y ∈ S}
    = {(a + b) + y | y ∈ S}
    = RHS

-/

def Coset [Magma α] (g: α) (S: Set α): Set α :=
  Set.image (λ a ↦ op g a) S

-- Given a set S, there is a relation that says a related to b if a + S = b + S.

def Coset.relation [Magma α] (S: Set α): Endorelation α :=
  λ a b ↦ Coset a S = Coset b S

-- TODO: simplify this? is just pullback of equality..

theorem Coset.equivalence [Magma α] (S: Set α): Equivalence (Coset.relation S) := by
  constructor
  · intro; apply Eq.refl
  · intro _ _ h; exact Eq.symm h
  · intro _ _ _ h1 h2; exact Eq.trans h1 h2

def Coset.quotient [Magma α] (S: Set α): Type u :=
  Quotient ⟨Coset.relation S, Coset.equivalence S⟩

-- If H is a subgroup and h ∈ H then h + H = H

theorem Coset.mem_self [G: Group α] {H: Set α} (hH: G.sub H) {h: α} (hh: h ∈ H): Coset h H = H := by
  /-
  Proof sketch:
  1. h + H ⊆ H:
    If x ∈ h + H then x = h + k for some k ∈ H.
    Then h + k ∈ H since H subgroup so x ∈ H.
  2. H ⊆ h + H:
    Suppose x ∈ H. Want to find k ∈ H s.t. x = h + k.
    Take k = -h + x. Then k ∈ H since both h, x are,
    and x = 0 + x
          = (h + -h) + x
          = h + (-h + x)
          = h + k.
  -/
  sorry

-- TODO: cosets form an action (is this necessary..?)



/-

The quotient group consists of cosets g + H, where [g] = g + H.

The unit element is 0 + H = H.

Addition of cosets given by (a + H) + (b + H) = (a + b) + H.

-/

/-

To define the quotient group we need to *lift* the operation of G to cosets.

Recall if `f: X → X → Y` is a "binary operation" taking values in Y
and ~ is an equivalence relation on X, then we can lift f to a map
  `(f/~) : (X/~) → (X/~) → Y`
if we can show:
  ∀ a a' b b', a ~ a' → b ∼ b' → f(a, b) = f(a', b')

-/

def QuotientGroup [G: Group α] (H: Set α) (h: G.normalSubgroup H): Group (Coset.quotient H) := {
  unit := Quotient.mk _ 0
  op := sorry
  identity := sorry
  assoc := sorry
  inv := sorry
  inverse := sorry
}
