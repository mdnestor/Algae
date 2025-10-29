
import Algae.Basic

-- A magma, i.e. a binary operation on a type.
class Magma (M: Type u) extends Add M

variable {M: Type u}

class AssociativeMagma (M: Type u) extends Magma M where
  add_associative: Associative add

theorem add_associative [AssociativeMagma M] (a b c: M): (a + b) + c = a + (b + c) := by
  exact AssociativeMagma.add_associative a b c

class CommutativeMagma (M: Type u) extends Magma M where
  add_commutative: Commutative add

theorem add_commutative [CommutativeMagma M] (a b: M): a + b = b + a := by
  exact CommutativeMagma.add_commutative a b



class MulMagma (M: Type u) extends Mul M

class AssociativeMulMagma (M: Type u) extends MulMagma M where
  mul_associative: Associative mul

theorem mul_associative [AssociativeMulMagma M] (a b c: M): (a * b) * c = a * (b * c) := by
  exact AssociativeMulMagma.mul_associative a b c

class CommutativeMulMagma (M: Type u) extends MulMagma M where
  mul_commutative: Commutative mul

theorem mul_commutative [CommutativeMulMagma M] (a b: M): a * b = b * a := by
  exact CommutativeMulMagma.mul_commutative a b
