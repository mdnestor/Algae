import Algae.Structure

variable {α: Type u}

class Submagma [Magma α] (S: Set α): Prop where
  op_closed: ∀ a b, a ∈ S → b ∈ S → op a b ∈ S

class Subpointed [Pointed α] (S: Set α): Prop where
  unit_mem: unit ∈ S

class Submonoid [Monoid α] (S: Set α) extends Submagma S, Subpointed S

class Subgroup [Group α] (S: Set α) extends Submonoid S where
  inv_closed: ∀ a, a ∈ S → inv a ∈ S
