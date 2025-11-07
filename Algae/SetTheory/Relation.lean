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
