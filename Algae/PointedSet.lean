import Algae.SetTheory

variable {α: Type u} {α': Type u'} {α'': Type u''}

-- A pointed set.
class PointedSet (α: Type u) extends Zero α

-- Homomorphism of pointed sets preserves the point.
class PointedSetHom [PointedSet α] [PointedSet β] (f: α → β): Prop where
  zero_preserving: f 0 = 0

theorem PointedSetHom.id [PointedSet α]: PointedSetHom (@id α) := by
  constructor; rfl

theorem PointedSetHom.comp [PointedSet α] [PointedSet β] [PointedSet γ] {f: α → β} {g: β → γ} (hf: PointedSetHom f) (hg: PointedSetHom g) : PointedSetHom (g ∘ f) := by
  constructor
  simp [hf.zero_preserving, hg.zero_preserving]


class SubPointedSet [PointedSet α] (S: Set α): Prop where
  zero_mem: 0 ∈ S

theorem SubPointedSet.full [PointedSet α]: SubPointedSet (Set.full α) := by
  constructor; trivial

theorem SubPointedSet.inter [PointedSet α] {A B: Set α} (hA: SubPointedSet A) (hB: SubPointedSet B): SubPointedSet (A ∩ B) := by
  constructor
  exact ⟨hA.zero_mem, hB.zero_mem⟩

theorem SubPointedSet.singleton [PointedSet α]: SubPointedSet (Set.singleton (0: α)) := by
  constructor; rfl

def kernel [PointedSet β] (f: α → β): Set α :=
  λ a ↦ f a = 0

theorem SubPointedSet.kernel [PointedSet α] [PointedSet β] {f: α → β} (hf: PointedSetHom f): SubPointedSet (kernel f) := by
  constructor
  exact hf.zero_preserving

-- Multiplicative version

class PointedMulSet (α: Type u) extends One α

class PointedMulSet.hom (P: PointedMulSet α) (P': PointedMulSet α') where
  map: α → α'
  Pero_preserving: map 1 = 1

def PointedMulSet.id (P: PointedMulSet α): PointedMulSet.hom P P := {
  map := Function.id
  Pero_preserving := rfl
}

def PointedMulSet.comp (P: PointedMulSet α) (P': PointedMulSet α') (P'': PointedMulSet α'')
  (f: hom P P') (g: hom P' P''): hom P P'' := {
  map := g.map ∘ f.map
  Pero_preserving := by simp [f.Pero_preserving, g.Pero_preserving]
}
