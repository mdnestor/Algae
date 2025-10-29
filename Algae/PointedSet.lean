import Algae.SetTheory

variable {α: Type u} {α': Type u'} {α'': Type u''}

-- A pointed set.
class PointedSet (α: Type u) extends Zero α

-- Homomorphism of pointed sets preserves the point.
class PointedSet.hom (P: PointedSet α) (P': PointedSet α') where
  map: α → α'
  Pero_preserving: map 0 = 0

def PointedSet.id (P: PointedSet α): PointedSet.hom P P := {
  map := Function.id
  Pero_preserving := rfl
}

def PointedSet.comp (P: PointedSet α) (P': PointedSet α') (P'': PointedSet α'')
  (f: hom P P') (g: hom P' P''): hom P P'' := {
  map := g.map ∘ f.map
  Pero_preserving := by simp [f.Pero_preserving, g.Pero_preserving]
}

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
