
import Algae.Basic

-- A magma, i.e. a binary operation on a type.
class Magma (α: Type u) where
  op: Op α

variable {α: Type u}

class AssociativeMagma (α: Type u) extends Magma α where
  associative: Associative op

class CommutativeMagma (α: Type u) extends Magma α where
  commutative: Commutative op
