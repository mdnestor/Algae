import Algae.SetTheory

variable {α: Type u}



def ZeroMem [Zero α] (S: Set α): Prop :=
  0 ∈ S

theorem ZeroMem.full [Zero α]: ZeroMem (Set.full α) := by
  trivial

theorem ZeroMem.singleton [Zero α]: ZeroMem (Set.singleton (0: α)) := by
  rfl

theorem ZeroMem.subset [Zero α] {A B: Set α} (hAB: A ⊆ B) (hA: ZeroMem A): ZeroMem B := by
  exact hAB 0 hA

theorem ZeroMem.inter [Zero α] {A B: Set α} (hA: ZeroMem A) (hB: ZeroMem B): ZeroMem (A ∩ B) := by
  trivial



def AddClosed [Add α] (S: Set α): Prop :=
  ∀ x y, x ∈ S → y ∈ S → x + y ∈ S

theorem AddClosed.full [Add α]: AddClosed (Set.full α) := by
  intro _ _ _ _
  trivial

theorem AddClosed.empty [Add α]: AddClosed (Set.empty α) := by
  intro _ _ _ _
  trivial

theorem AddClosed.inter [Add α] {A B: Set α} (hA: AddClosed A) (hB: AddClosed B): AddClosed (A ∩ B) := by
  intro a b ha hb
  constructor
  exact hA _ _ ha.left hb.left
  exact hB _ _ ha.right hb.right



def NegClosed [Neg α] (S: Set α): Prop :=
  ∀ x, x ∈ S → -x ∈ S

theorem NegClosed.full [Neg α]: NegClosed (Set.full α) := by
  intro _ _
  trivial

theorem NegClosed.empty [Neg α]: NegClosed (Set.empty α) := by
  intro _ _
  trivial

theorem NegClosed.inter [Neg α] {A B: Set α} (hA: NegClosed A) (hB: NegClosed B): NegClosed (A ∩ B) := by
  intro a ha
  constructor
  exact hA _ ha.left
  exact hB _ ha.right
