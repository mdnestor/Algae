import Algae.GroupTheory.Group
import Algae.GroupTheory.Action

variable {α: Type u}

open Group

-- The (left) conjugation by an element g ∈ G of a group is the map a ↦ gag⁻¹.
-- This is a left action of the group on itself.
-- (The map a ↦ g⁻¹ag is the right conjugation since it corresponds to a right action.)

def Conjugate [Group α] (g: α): α → α :=
  λ a ↦ g + a + -g

def Group.conjugation [G: Group α]: G.action α := {
  act := Conjugate
  op := by
    intro a b x
    simp [Conjugate]
    apply Eq.symm
    calc
       ((a + b) + x) + -(a + b)
       _ = ((a + b) + x) + (-b + -a) := by rw [inv_op]
       _ = a + (b + x + -b) + -a := by simp [op_assoc]
  id := by
    intro
    rw [Conjugate]
    rw [inv_unit, op_unit_left, op_unit_right]
}

-- A normal subgroup is one which is invariant under conjugation.

class Group.normalSubgroup [G: Group α] (S: Set α) extends toSubgroup: G.sub S where
  conj_invariant: Group.conjugation.invariant_set S

-- In a commutative group, conjugation is trivial since gag⁻¹ = agg⁻¹ = a.

theorem CommGroup.conjugate_trivial [CommGroup α] (g: α): Conjugate g = Function.id := by
  funext
  rw [Conjugate, op_comm, ←op_assoc, op_inv_left, op_unit_left, Function.id]

-- Thus in a commutative group, every subgroup is normal.

theorem CommGroup.subgroup_normal [G: CommGroup α] {S: Set α} (h: G.sub S): G.normalSubgroup S := by
  constructor
  intro _ _ hx
  simp [Group.conjugation, CommGroup.conjugate_trivial]
  exact hx



-- Given an element a and set S, the (left) coset is defined a • S = {a + s | s ∈ S}.

def Coset [Magma α] (g: α) (S: Set α): Set α :=
  Set.image (λ a ↦ g + a) S

-- The action which sends (a, H) ↦ aH and satisfies (a + b) • S = a • (b • S).

def Group.coset_action (G: Group α): G.action (Set α) := {
  act := λ a H ↦ Set.image (λ x ↦ a + x) H
  op := by
    intro a b H
    funext z
    simp
    constructor
    intro ⟨x, ⟨y, h1, h2⟩, h3⟩
    simp_all [Set.image]
    sorry
    intro ⟨x, h1, h2⟩
    simp_all [Set.image]
    sorry
  id := by
    intro H
    simp [op_unit_left]
    sorry -- trivial
}

-- The coset action which sends (g, H) ↦ gHg⁻¹ and is also a left action.

def Group.coset_conjugate (G: Group α): G.action (Set α) := {
  act := λ a H ↦ Set.image (λ x ↦ Conjugate a x) H
  op := by
    intro a b H
    funext z
    simp
    constructor
    intro ⟨x, ⟨y, h1, h2⟩, h3⟩
    simp_all [Set.image, Conjugate]
    sorry
    intro ⟨x, h1, h2⟩
    simp_all [Set.image, Conjugate]
    sorry
  id := by
    intro H
    sorry
}

-- Given a set S, the equivalence relation a ~ b if a • S = b • S.

def coset_relation [Magma α] (S: Set α): Endorelation α :=
  λ a b ↦ Coset a S = Coset b S

theorem coset_equivalence [Magma α] (S: Set α): Equivalence (coset_relation S) := by
  constructor
  · intro; apply Eq.refl
  · intro _ _ h; exact Eq.symm h
  · intro _ _ _ h1 h2; exact Eq.trans h1 h2

def Coset.quotient [Magma α] (S: Set α): Type u :=
  Quotient ⟨coset_relation S, coset_equivalence S⟩

/-

Lifting the operations of a group to operations on cosets.

First example: if a ∼ b, i.e. aH = bH, show that a⁻¹ ∼ b⁻¹, i.e. a⁻¹H = b⁻¹H.

Multiplicative notation for convenience. The paper proof is:

a⁻¹H = a⁻¹ (b H b⁻¹)  conjugate by b
     = a⁻¹ (b H) b⁻¹
     = a⁻¹ (a H) b⁻¹  assumption
     = (a⁻¹ a) H b⁻¹
     = H b⁻¹
     = (b⁻¹ H b) b⁻¹  conjugate by b⁻¹
     = b⁻¹ H b b⁻¹
     = b⁻¹ H

However we don't necessarily want to use right cosets.
Instead we can exclusively use left cosets and conjugations.
Let aH denote the coset and φ(g, H) = gHg⁻¹ denote conjugation by g.
The idea is to "balance" the equation each time a right coset appears via:

  Ha = aa⁻¹Ha = a φ(a⁻¹, H)

For a normal subgroup φ(g, H) = H for all g. So the argument above becomes

a⁻¹H = a⁻¹    (b H b⁻¹)              = a⁻¹ φ(b, H)
     = a⁻¹b⁻¹ (b (bH) b⁻¹)           = a⁻¹b⁻¹ φ(b, bH)
     = a⁻¹b⁻¹ (b (aH) b⁻¹)           = a⁻¹b⁻¹ φ(b, aH)
     = a⁻¹b⁻¹ bab⁻¹ = b⁻¹H
     = a⁻¹b⁻¹ (b (a (b⁻¹ H b)) b⁻¹)  = a⁻¹b⁻¹ φ(b, a φ(b⁻¹, H)
     = ...
      = H

So the needed lemmas are:
- φ(x, H) = x⁻¹ φ(x, xH)
- φ(x⁻¹, H) = x φ(x⁻¹, x⁻¹H)
- φ(x, yH) = x(yH)x⁻¹ = xyHx⁻¹ = xyx⁻¹H
- also g(aH)g⁻¹ = aH

-/

theorem Coset.lift_inverse [G: Group α] (H: Set α) (hH: G.normalSubgroup H) (a b: α) (hab: Coset a H = Coset b H):
  Coset (-a) H = Coset (-b) H := by

  sorry

def QuotientGroup [G: Group α] (H: Set α) (h: G.normalSubgroup H): Group (Coset.quotient H) := {
  unit := Quotient.mk _ unit
  op := sorry
  identity := sorry
  assoc := sorry
  inv := sorry
  inverse := sorry
}
