import Algae.Group

variable {α: Type u}

def DistribLeft (add mul: Op α): Prop :=
  ∀ a b c, mul a (add b c) = add (mul a b) (mul a c)

def DistribRight (add mul: Op α): Prop :=
  DistribLeft add (λ a b ↦ mul b a)

def Distrib (add mul: Op α): Prop :=
  DistribLeft add mul ∧ DistribRight add mul

class Ring (α: Type u) where
  add_group: CommutativeGroup α
  mul_monoid: Monoid α
  distributive: Distributive mul_monoid.op add_group.op

def Ring.add (R: Ring α): Op α :=
  R.add_group.op

def Ring.mul (R: Ring α): Op α :=
  R.mul_monoid.op

def Ring.neg (R: Ring α): α → α :=
  R.add_group.inv

def Ring.zero (R: Ring α): α :=
  R.add_group.unit

def Ring.one (R: Ring α): α :=
  R.mul_monoid.unit

-- Zero is absorbing wrt. multiplication: 0 * a = 0 * a = 0
theorem Ring.mul_absorbing (R: Ring α): Absorbs R.mul R.zero := by
  sorry

-- (-1) * a = -a.
theorem Ring.mul_neg_one (R: Ring α) (a: α): R.mul (R.neg R.one) a = R.neg a := by
  sorry

-- If 0 = 1 the ring is trivial.
theorem Ring.zero_eq_one_trivial {R: Ring α} (h: R.zero = R.one): ∀ a b: α, a = b := by
  sorry

class CommutativeRing (α: Type u) where
  add: CommutativeGroup α
  mul: CommutativeMonoid α
  distrib: Distrib add.op mul.op

def CommutativeRing.zero (R: CommutativeRing α): α :=
  R.add.unit

def CommutativeRing.one (R: CommutativeRing α): α :=
  R.mul.unit
