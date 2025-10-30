
import Algae.Basic
import Algae.SetTheory

variable {M: Type u}


-- A magma, i.e. a binary operation on a type.
class Magma (M: Type u) extends Add M

class AssociativeMagma (M: Type u) extends Magma M where
  add_associative: Associative add

theorem add_associative [AssociativeMagma M] (a b c: M): (a + b) + c = a + (b + c) := by
  exact AssociativeMagma.add_associative a b c

class CommutativeMagma (M: Type u) extends Magma M where
  add_commutative: Commutative add

theorem add_commutative [CommutativeMagma M] (a b: M): a + b = b + a := by
  exact CommutativeMagma.add_commutative a b

class MagmaHom [Magma α] [Magma β] (f: α → β): Prop where
  add_preserving: ∀ a₁ a₂: α, f (a₁ + a₂) = f a₁ + f a₂

theorem MagmaHom.id [Magma α]: MagmaHom (@id α) := by
  constructor; intros; rfl

theorem MagmaHom.comp [Magma α] [Magma β] [Magma γ] {f: α → β} {g: β → γ} (hf: MagmaHom f) (hg: MagmaHom g) : MagmaHom (g ∘ f) := by
  constructor
  simp [hf.add_preserving, hg.add_preserving]





class SubMagma [Magma M] (S: Set M): Prop where
  add_closed: ∀ a b, a ∈ S → b ∈ S → a + b ∈ S

theorem SubMagma.full [Magma M]: SubMagma (Set.full M) := by
  constructor; intros; trivial

theorem SubMagma.empty [Magma M]: SubMagma (Set.empty M) := by
  constructor; intros; trivial

theorem SubMagma.inter [Magma M] {A B: Set M} (hA: SubMagma A) (hB: SubMagma B): SubMagma (A ∩ B) := by
  constructor
  intro _ _  ha hb
  constructor
  exact hA.add_closed _ _ (Set.inter_left ha) (Set.inter_left hb)
  exact hB.add_closed _ _ (Set.inter_right ha) (Set.inter_right hb)


-- The center is the set of elements
-- that commute with every other element
def Center (M: Type u) [Magma M]: Set M :=
  λ z ↦ ∀ m, z + m = m + z

theorem center_submagma [AssociativeMagma M]: SubMagma (Center M) := by
  constructor
  intro x y hx hy m
  calc
    x + y + m
    _ = x + (y + m) := by rw [add_associative]
    _ = x + (m + y) := by rw [hy]
    _ = x + m + y := by rw [add_associative]
    _ = m + x + y := by rw [hx]
    _ = m + (x + y) := by rw [add_associative]

class MulMagma (M: Type u) extends Mul M

class AssociativeMulMagma (M: Type u) extends MulMagma M where
  mul_associative: Associative mul

theorem mul_associative [AssociativeMulMagma M] (a b c: M): (a * b) * c = a * (b * c) := by
  exact AssociativeMulMagma.mul_associative a b c

class CommutativeMulMagma (M: Type u) extends MulMagma M where
  mul_commutative: Commutative mul

theorem mul_commutative [CommutativeMulMagma M] (a b: M): a * b = b * a := by
  exact CommutativeMulMagma.mul_commutative a b
