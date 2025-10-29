
variable {α: Type u} {β: Type v}

def Op (α: Type u): Type u :=
  α → α → α

def LeftIdentity (op: Op α) (e: α): Prop :=
  ∀ a, op e a = a

def RightIdentity (op: Op α) (e: α): Prop :=
  ∀ a, op a e = a

def Identity (op: Op α) (e: α): Prop :=
  LeftIdentity op e ∧ RightIdentity op e

def Associative (op: Op α): Prop :=
  ∀ a b c, op (op a b) c = op a (op b c)

def Commutative (op: Op α): Prop :=
  ∀ a b, op a b = op b a

def Inverses (op: Op α) (a b e: α): Prop :=
  op a b = e ∧ op b a = e

def LeftInverse (op: Op α) (inv: α → α) (e: α): Prop :=
  ∀ a, op (inv a) a = e

def RightInverse (op: Op α) (inv: α → α) (e: α): Prop :=
  ∀ a, op a (inv a) = e

def Inverse (op: Op α) (inv: α → α) (e: α): Prop :=
  LeftInverse op inv e ∧ RightInverse op inv e

def DistributiveLeft (op₁ op₂: Op α): Prop :=
  ∀ a b c, op₁ a (op₂ b c) = op₂ (op₁ a b) (op₁ a c)

def DistributiveRight (op₁ op₂: Op α): Prop :=
  ∀ a b c, op₁ (op₂ a b) c = op₂ (op₁ a c) (op₁ b c)

def Distributive (op₁ op₂: Op α): Prop :=
  DistributiveLeft op₁ op₂ ∧ DistributiveRight op₁ op₂

def AbsorbsLeft (op: Op α) (z: α): Prop :=
  ∀ a, op z a = z

def AbsorbsRight (op: Op α) (z: α): Prop :=
  ∀ a, op a z = z

def Absorbs (op: Op α) (z: α): Prop :=
  AbsorbsLeft op z ∧ AbsorbsRight op z
