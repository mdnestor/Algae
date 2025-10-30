import Algae.Subobject

variable {α: Type u} {β: Type v}

def Kernel [Zero β] (f: α → β): Set α :=
  λ a => f a = 0
