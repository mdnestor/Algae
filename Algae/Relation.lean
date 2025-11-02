import Algae.SetTheory

variable {α: Type u} {β: Type w}

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

def Transitive (R: Endorelation α): Prop :=
  ∀ {a b c}, R a b → R b c → R a c

class Preorder (R: Endorelation α): Prop where
  reflexive: Reflexive R
  transitive: Transitive R

def Symmetric (R: Endorelation α): Prop :=
  ∀ {a b}, R a b → R b a

def Relation.toSet (R: Relation α β): Set (α × β) :=
  λ (a, b) ↦ R a b

def Set.toRelation (S: Set (α × β)): Relation α β :=
  λ a b ↦ (a, b) ∈ S

instance: Endorelation (Relation α β) :=
  λ R₁ R₂ ↦ ∀ a b, R₁ a b → R₂ a b
