import Algae.Monoid

variable {α: Type u}

-- TODO: same for unital magma, we might want 2 fields for left/right inverse...
class Group (α: Type u) extends Monoid α, Inv α where
  inverse: Inverse op inv unit

-- In a group we can define integer powers.
def Group.zpow {G: Group α} (a: α) (k: Int): α :=
  match k with
  | Int.ofNat n => G.npow a n
  | Int.negSucc n => G.npow (G.inv a) n


-- todo: show the set of permutations on a set form a group


class CommutativeGroup (α: Type u) extends Group α, CommutativeMagma α

namespace Group

-- Sanity check to make sure everything works.
theorem Group.square_self_unit {G: Group α} {a: α} (h: G.npow a 2 = a): a = G.unit := by
  calc
    a = G.op G.unit a               := by rw [G.identity.left]
    _ = G.op (G.op (G.inv a) a) a   := by rw [G.inverse.left]
    _ = G.op (G.inv a) (G.op a a)   := by rw [G.associative]
    _ = G.op (G.inv a) (G.npow a 2) := by rw [G.npow_two]
    _ = G.op (G.inv a) a            := by rw [h]
    _ = G.unit                      := by rw [G.inverse.left]


-- TODO theorem: if a*b = e then a = b⁻¹.


-- alternatively could show the map a ↦ a⁻¹ is an involution?
theorem Group.double_inverse {G: Group α} (a: α): G.inv (G.inv a) = a := by
  sorry

-- "socks shoes" property
theorem Group.socks_shoes {G: Group α} (a b: α): G.inv (G.op a b) = G.op (G.inv b) (G.inv a) := by
  sorry

-- Fix a ∈ G. Then the map G → G defined by b ↦ a * b is a bijection (permutation) on G.
theorem Group.self_bijective {G: Group α} (a: α): Function.Bijective (λ b ↦ G.op a b) := by
  sorry
