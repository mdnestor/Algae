import Algae.SetTheory.Function
import Algae.SetTheory.Subset

variable {α: Type u} {β: Type v} {γ: Type w}

def Relation (α: Type u) (β: Type v): Type (max u v) :=
  α → β → Prop

def Relation.fiber (R: Relation α β) (b: β): Set α :=
  λ a ↦ R a b

def Relation.cofiber (R: Relation α β) (a: α): Set β :=
  λ b ↦ R a b

def Endorelation (α: Type u): Type u :=
  Relation α α

def Reflexive (R: Endorelation α): Prop :=
  ∀ a, R a a

def Irreflexive (R: Endorelation α): Prop :=
  ∀ a, ¬ R a a

def Transitive (R: Endorelation α): Prop :=
  ∀ {a b c}, R a b → R b c → R a c

def Symmetric (R: Endorelation α): Prop :=
  ∀ {a b}, R a b → R b a

def Antisymmetric (R: Endorelation α): Prop :=
  ∀ {a b}, R a b → R b a → a = b

def Total (R: Endorelation α): Prop :=
  ∀ {a b}, R a b ∨ R b a

-- Notation

instance [LE α]: LT α := {
  lt := λ a b ↦ a ≤ b ∧ ¬ b ≤ a
}

class Bottom (α: Type u) extends LE α where
  bottom: α
  bottom_le: ∀ x, bottom ≤ x

notation "⊥" => Bottom.bottom

class Top (α: Type u) extends LE α where
  top: α
  top_ge: ∀ x, x ≤ top

notation "⊤" => Top.top



def UpperBound (R: Relation α β) (S: Set α) (b: β): Prop :=
  ∀ a, a ∈ S → R a b

def LowerBound (R: Relation α β) (S: Set β) (b: α): Prop :=
  UpperBound (switch R) S b

def UpperBounds (R: Relation α β) (S: Set α): Set β :=
  λ b ↦ UpperBound R S b

def GenLeastUpperBound (R: Relation α β) (R': Endorelation β) (S: Set α) (b: β): Prop :=
  UpperBound R S b ∧ LowerBound R' (UpperBounds R S) b

def LeastUpperBound (R: Endorelation α) (S: Set α) (b: α): Prop :=
  GenLeastUpperBound R R S b

theorem GenLeastUpperBound.unique (R: Relation α β) (R': Endorelation β) (S: Set α) (b b': β)
  (hR': Antisymmetric R') (h: GenLeastUpperBound R R' S b) (h': GenLeastUpperBound R R' S b'): b = b' := by
  apply hR'
  · exact h.right b' h'.left
  · exact h'.right b h.left



def Relation.pullback (f: α → α') (g: β → β') (r: Relation α' β'): Relation α β :=
  λ a b ↦ r (f a) (g b)

def Endorelation.pullback (f: α → β) (r: Endorelation β): Endorelation α :=
  λ a b ↦ r (f a) (f b)

theorem Endorelation.pullback_reflexive (f: α → β) {r: Endorelation β} (hr: Reflexive r): Reflexive (pullback f r) := by
  intro; apply hr

theorem Endorelation.pullback_transitive (f: α → β) {r: Endorelation β} (hr: Transitive r): Transitive (pullback f r) := by
  exact hr

theorem Endorelation.pullback_symmetric (f: α → β) {r: Endorelation β} (hr: Symmetric r): Symmetric (pullback f r) := by
  exact hr

theorem Endorelation.pullback_equivalence (f: α → β) {r: Endorelation β} (hr: Equivalence r): Equivalence (pullback f r) := by
  constructor
  · exact pullback_reflexive f hr.refl
  · exact pullback_symmetric f hr.symm
  · sorry

def Endorelation.pullback_eq (f: α → β): Endorelation α :=
  Endorelation.pullback f Eq

def Endorelation.map_equivalence (f: α → β): Equivalence (pullback_eq f) := by
  apply Endorelation.pullback_equivalence f
  constructor
  intro; rfl
  sorry
  sorry

class Preorder (X: Type u) extends LE X where
  reflexive: ∀ x: X, x ≤ x
  transitive: ∀ x y z: X, x ≤ y → y ≤ z → x ≤ z

class PartialOrder (X: Type u) extends Preorder X where
  antisymmetric: ∀ x y: X, x ≤ y → y ≤ x → x = y

class Lattice (X: Type u) extends PartialOrder X, Min X, Max X where
  max_le_left: ∀ x y, x ≤ max x y
  max_le_right: ∀ x y, y ≤ max x y
  max_lub: ∀ x y z, x ≤ z → y ≤ z → max x y ≤ z
  min_le_left: ∀ x y, min x y ≤ x
  min_le_right: ∀ x y, min x y ≤ y
  min_glb: ∀ x y z, z ≤ x → z ≤ y → z ≤ min x y
