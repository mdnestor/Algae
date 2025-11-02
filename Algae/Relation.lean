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

def Symmetric (R: Endorelation α): Prop :=
  ∀ {a b}, R a b → R b a
