import Algae.SetTheory

variable {α: Type u} {β: Type v} {γ: Type w}

def ZeroPreserving [Zero α] [Zero β] (f: α → β): Prop :=
  f 0 = 0

theorem ZeroPreserving.id [Zero α]: ZeroPreserving (@Function.id α) := by
  rfl

theorem ZeroPreserving.comp [Zero α] [Zero β] [Zero γ]
  {f: α → β} {g: β → γ} (hf: ZeroPreserving f) (hg: ZeroPreserving g):
  ZeroPreserving (g ∘ f) := by
  simp [ZeroPreserving]
  rw [hf, hg]



def AddPreserving [Add α] [Add β] (f: α → β): Prop :=
  ∀ a b, f (a + b) = f a + f b

theorem AddPreserving.id [Add α]: AddPreserving (@Function.id α) := by
  intro _ _
  rfl

theorem AddPreserving.comp [Add α] [Add β] [Add γ]
  {f: α → β} {g: β → γ} (hf: AddPreserving f) (hg: AddPreserving g):
  AddPreserving (g ∘ f) := by
  intro _ _
  simp
  rw [hf, hg]



def NegPreserving [Neg α] [Neg β] (f: α → β): Prop :=
  ∀ a, f (-a) = -(f a)

theorem NegPreserving.id [Neg α]: NegPreserving (@Function.id α) := by
  intro _
  rfl

theorem NegPreserving.comp [Neg α] [Neg β] [Neg γ]
  {f: α → β} {g: β → γ} (hf: NegPreserving f) (hg: NegPreserving g):
  NegPreserving (g ∘ f) := by
  intro _
  simp
  rw [hf, hg]
