import Algae.SetTheory

variable {α: Type u} {α': Type u'} {α'': Type u''}

-- A pointed set.
class PointedSet (α: Type u) where
  unit: α

-- Homomorphism of pointed sets preserves the point.
class PointedSet.hom (P: PointedSet α) (P': PointedSet α') where
  map: α → α'
  unit_preserving: map P.unit = P'.unit

def PointedSet.id (P: PointedSet α): PointedSet.hom P P := {
  map := Function.id
  unit_preserving := rfl
}

def PointedSet.comp (P: PointedSet α) (P': PointedSet α') (P'': PointedSet α'')
  (f: hom P P') (g: hom P' P''): hom P P'' := {
  map := g.map ∘ f.map
  unit_preserving := by simp [f.unit_preserving, g.unit_preserving]
}
