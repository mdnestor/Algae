import Algae.GroupTheory.Monoid

variable {α: Type u} {β: Type v} {γ: Type w}



/-

A group is a monoid with inverses.

-/

class Group (α: Type u) extends Monoid α where
  inv: α → α
  inverse: Inverse op inv unit

class CommGroup (α: Type u) extends Group α, CommMonoid α




-- Introduces notation +, 0, and - for groups.
export Group (inv)
namespace Group
scoped instance [Magma α]: Add α := ⟨op⟩
scoped instance [Pointed α]: Zero α := ⟨unit⟩
scoped instance [Group α]: Neg α := ⟨inv⟩
def opinv [Group α] (a b: α): α := a + -b
scoped instance [Group α]: Sub α := ⟨opinv⟩
scoped instance [Group α]: SMul Nat α := ⟨Monoid.ngen⟩
def zgen [Group α] (k: Int) (a: α): α :=
  match k with
  | Int.ofNat n => n • a
  | Int.negSucc n => n.succ • -a
instance [Group α]: SMul Int α := ⟨zgen⟩
end Group

open Group



-- Unpacking axioms with notation.

theorem op_inv_left [Group α] (a: α): -a + a = 0 := by
  exact Group.inverse.left a

theorem op_inv_right [Group α] (a: α): a + -a = 0 := by
  exact Group.inverse.right a

theorem inverses_inv [Group α] (a: α): inverses a (-a) := by
  constructor
  exact op_inv_right a
  exact op_inv_left a

theorem op_cancel_left [Group α] {a b c: α} (h: a + b = a + c): b = c := by
  calc
    b
    _ = 0 + b        := by rw [op_unit_left]
    _ = -a + a + b   := by rw [op_inv_left]
    _ = -a + (a + b) := by rw [op_assoc]
    _ = -a + (a + c) := by rw [h]
    _ = -a + a + c   := by rw [op_assoc]
    _ = 0 + c        := by rw [op_inv_left]
    _ = c            := by rw [op_unit_left]

theorem op_cancel_right [Group α] {a b c: α} (h: a + c = b + c): a = b := by
  calc
    a
    _ = a + 0        := by rw [op_unit_right]
    _ = a + (c + -c) := by rw [op_inv_right]
    _ = a + c + -c   := by rw [op_assoc]
    _ = b + c + -c   := by rw [h]
    _ = b + (c + -c) := by rw [op_assoc]
    _ = b + 0        := by rw [op_inv_right]
    _ = b            := by rw [op_unit_right]

theorem op_unit_inverses [Group α] {a b: α} (h: a + b = 0): -a = b := by
  have: -a + a + b = -a := by rw [op_assoc, h, op_unit_right]
  rw [←this, op_inv_left, op_unit_left]

theorem inv_unit [Group α]: -(0: α) = 0 := by
  apply op_unit_inverses
  apply op_unit_left

theorem inv_inv [Group α] (a: α): -(-a) = a := by
  apply op_cancel_right (c := -a)
  rw [op_inv_left, op_inv_right]

theorem opinv_self [Group α] (a: α): a - a = 0 := by
  apply op_inv_right

theorem inv_invop [Group α] (a b: α): -(a - b) = b - a := by
  apply op_unit_inverses
  calc
    a - b + (b - a)
    _ = a + -b + (b + -a)   := by rfl
    _ = a + (-b + (b + -a)) := by rw [op_assoc]
    _ = a + (-b + b + -a)   := by rw [op_assoc]
    _ = a + (0 + -a)        := by rw [op_inv_left]
    _ = a + -a              := by rw [op_unit_left]
    _ = 0                   := by rw [op_inv_right]

-- In a group we can define integer multiplication via
-- 0 * a = 0, 1 * a = a, 2 * a = a + a, ... and -1 * a = 1 * -a, -2 * a = 2 * (-a), ...

theorem ngen_neg_left [Group α] (a: α) (n: Nat): n • (-a) + n • a = 0 := by
  apply ngen_inverses n
  exact op_inv_left a

theorem ngen_neg_right [Group α] (a: α) (n: Nat): n • a + n • -a = 0 := by
  apply ngen_inverses n
  exact op_inv_right a

theorem zgen_zero [Group α] (a: α): (0: Int) • a = (0: α) := by
  rfl

theorem ngen_inv [Group α] (a: α) (n: Nat): (n • a) + (n • -a) = 0 := by
  induction n with
  | zero => simp [ngen_zero, op_unit_left]
  | succ p hp =>
    rw [Nat.add_comm, ←ngen_add, ngen_one]
    rw [Nat.add_comm, ←ngen_add, ngen_one]
    rw [op_assoc, ←op_assoc (p • a)]
    rw [hp, op_unit_left, op_inv_right]

theorem zgen_neg' [Group α] (a: α) (n: Int): -(n • a) = n • -a := by
  apply op_unit_inverses
  induction n <;> apply ngen_inv

theorem zgen_add [Group α] (a: α) (m n: Int): m • a + n • a = (m + n) • a := by
  induction m with
  | ofNat p => induction p with
    | zero => simp [zgen_zero, op_unit_left]
    | succ p hp => sorry
  | negSucc p => sorry

theorem zgen_neg [Group α] (a: α) (n: Int): n • (-a) = -n • a := by
  induction n with
  | ofNat p => calc
    Int.ofNat p • -a
    _ = p • -a := by rfl
    _ = -Int.ofNat p • a := sorry
  | negSucc p => sorry



theorem square_self_zero [Group α] {a: α} (h: 2 • a = a): a = 0 := by
  calc
    a
    _ = 0 + a        := by rw [op_unit_left]
    _ = (-a + a) + a := by rw [op_inv_left]
    _ = -a + (a + a) := by rw [op_assoc]
    _ = -a + (2 • a) := by rw [ngen_two]
    _ = -a + a       := by rw [h]
    _ = 0            := by rw [op_inv_left]


-- "Socks shoes" property
theorem inv_op [Group α] (a b: α): -(a + b) = -b + -a := by
  repeat rw [←neg_eq]
  apply op_cancel_right (c := (a + b))
  rw [op_inv_left]
  apply Eq.symm
  calc
    -b + -a + (a + b)
    _ = -b + (-a + (a + b)) := by rw [op_assoc]
    _ = -b + (-a + a + b)   := by rw [op_assoc]
    _ = -b + (0 + b)        := by rw [op_inv_left]
    _ = -b + b              := by rw [op_unit_left]
    _ = 0                   := by rw [op_inv_left]



-- A group homomorphism is a monoid homomorphism which also preserves inverses.

class Group.hom (G₁: Group α) (G₂: Group β)
  extends toMonoidHom: Monoid.hom G₁.toMonoid G₂.toMonoid where
  inv_preserving: ∀ a, map (-a) = -(map a)

-- A subgroup is a submonoid which is also closed under inverses.

class Group.sub (G: Group α) (S: Set α) extends G.toMonoid.sub S where
  inv_closed: ∀ a, a ∈ S → -a ∈ S


-- The image of a group homomorphism is a subgroup.

theorem Group.hom.image_sub (G₁: Group α) (G₂: Group β) (f: hom G₁ G₂): G₂.sub (Set.range f.map) := {
  unit_mem := (Monoid.hom.image_sub f.toMonoidHom).unit_mem
  op_closed := (Monoid.hom.image_sub f.toMonoidHom).op_closed
  inv_closed := by
    intro _ ⟨a, ha⟩
    rw [←ha, ←f.inv_preserving]
    apply Set.range_mem
}

-- The kernel is a subgroup.

theorem Group.kernel_sub (G₁: Group α) (G₂: Group β) (f: hom G₁ G₂): G₁.sub f.kernel := {
  unit_mem := (Monoid.kernel_sub f.toMonoidHom).unit_mem
  op_closed := (Monoid.kernel_sub f.toMonoidHom).op_closed
  inv_closed := by
    intro x hx
    calc
      f.map (-x)
      _ = -(f.map x) := by rw [f.inv_preserving]
      _ = -0 := by rw [hx]
      _ = 0 := by rw [inv_unit]
}

-- The opposite group.

def Group.opposite (G: Group α): Group α := {
  op := Group.toMonoid.opposite.op
  identity := Group.toMonoid.opposite.identity
  assoc := Group.toMonoid.opposite.assoc
  inv := inv
  inverse := ⟨inverse.right, inverse.left⟩
}
