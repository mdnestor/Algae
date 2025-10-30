import Algae.Basic
import Algae.Morphism
import Algae.Subobject
import Algae.Kernel

variable {M : Type u} {A: Type u}


class Monoid (A: Type u) extends Zero A, Add A where
  add_zero: Identity add 0
  add_assoc: Associative add

theorem add_zero_left [Monoid A] (a: A): 0 + a = a := by
  exact Monoid.add_zero.left a

theorem add_zero_right [Monoid M] (a: M): a + 0 = a := by
  exact Monoid.add_zero.right a

theorem add_assoc [Monoid M] (a b c: M): a + b + c = a + (b + c) := by
  exact Monoid.add_assoc a b c

def Monoid.inverses [Monoid M] (a b: M): Prop :=
  Inverses Add.add a b 0

def Monoid.inverses_iff [Monoid M] (a b: M):
  inverses a b ↔ a + b = 0 ∧ b + a = 0 := by
  rfl

/-

In a monoid we can "multiply" by natural numers a la `n • a` by

0 • a = 0
1 • a = a
2 • a = a + a
3 • a = a + a + a
4 • a = a + a + a + a

etc...

-/

def Monoid.smul [Monoid A] (n: Nat) (a: A): A :=
  match n with
  | Nat.zero => 0
  | Nat.succ p => smul p a + a

instance [Monoid A]: SMul Nat A := {
  smul := Monoid.smul
}

-- Simple theorems about npow.
theorem Monoid.smul_zero [Monoid A] (a: A): 0 • a = 0 := by
  rfl

theorem Monoid.smul_succ [Monoid A] (a: A) (n: Nat): n.succ • a = n • a + a := by
  rfl

theorem Monoid.smul_one [Monoid A] (a: A): 1 • a = a := by
  rw [smul_succ, smul_zero]
  exact add_zero_left a

theorem Monoid.npow_two [Monoid M] (a: M): 2 • a = a + a := by
  rw [smul_succ, smul_one]



class MonoidHom [Monoid α] [Monoid β] (f: α → β): Prop where
  zero_preserving: ZeroPreserving f
  add_preserving: AddPreserving f

theorem MonoidHom.id [Monoid α]: MonoidHom (@id α) := {
  zero_preserving := ZeroPreserving.id
  add_preserving := AddPreserving.id
}

theorem MonoidHom.comp [Monoid A] [Monoid B] [Monoid C]
  {f: A → B} {g: B → C} (hf: MonoidHom f) (hg: MonoidHom g): MonoidHom (g ∘ f) := {
  zero_preserving := ZeroPreserving.comp hf.zero_preserving hg.zero_preserving
  add_preserving := AddPreserving.comp hf.add_preserving hg.add_preserving
}



class Submonoid [Monoid α] (S: Set α): Prop where
  zero_mem: ZeroMem S
  add_closed: AddClosed S

theorem Submonoid.full [Monoid α]: Submonoid (Set.full α) := {
  zero_mem := ZeroMem.full
  add_closed := AddClosed.full
}

theorem Submonoid.singleton [Monoid α]: Submonoid (Set.singleton (0: α)) := {
  zero_mem := ZeroMem.singleton
  add_closed := by
    intro a b ha hb
    calc
      a + b
      _ = 0 + 0 := by rw [ha, hb]
      _ = 0 := by rw [add_zero_left]
}

def Submonoid.kernel [Monoid α] [Monoid β] {f: α → β} (hf: MonoidHom f): Submonoid (Kernel f) := {
  zero_mem := hf.zero_preserving
  add_closed := by
    intro a b ha hb
    calc
      f (a + b)
        = f a + f b := by rw [hf.add_preserving]
      _ = 0 + 0     := by rw [ha, hb]
      _ = 0         := by rw [add_zero_left]
}

theorem inverses_unique [Monoid M] {a b b': M}
  (h: Monoid.inverses a b) (h': Monoid.inverses a b'): b = b' := by
  simp_all [Monoid.inverses_iff]
  calc
    b = b + 0        := by rw [add_zero_right]
    _ = b + (a + b') := by rw [h'.left]
    _ = (b + a) + b' := by rw [add_assoc]
    _ = 0 + b'       := by rw [h.right]
    _ = b'           := by rw [add_zero_left]

-- On any type X the set of functions X → X is a monoid.
def Endomonoid (M: Type u): Monoid (M → M) := {
  add := λ f g ↦ g ∘ f
  zero := Function.id
  add_zero := by constructor <;> exact congrFun rfl
  add_assoc := by intro _ _ _ ; rfl
}

-- List M is a monoid.
def FreeMonoid (M : Type u) : Monoid (List M) := {
  add := List.append
  zero := List.nil
  add_zero := by constructor <;> (simp [LeftIdentity, RightIdentity]; rfl)
  add_assoc := by intro; simp
}


class CommMonoid (A : Type u) extends Monoid A where
  add_comm: ∀ a b: A, a + b = b + a

theorem add_comm [CommMonoid A] (a b: A): a + b = b + a := by
  exact CommMonoid.add_comm a b


example (M: Type u): CommMonoid (Set M) := {
  add := Set.union
  zero := Set.empty M
  add_zero := by exact Set.union_identity
  add_assoc := by exact Set.union_assoc
  add_comm := by exact Set.union_comm
}

example (M: Type u): CommMonoid (Set M) := {
  add := Set.inter
  zero := Set.full M
  add_zero := by exact Set.inter_identity
  add_assoc := by exact Set.inter_assoc
  add_comm := by exact Set.inter_comm
}

example: CommMonoid Nat := {
  add := Nat.add
  zero := 0
  add_zero := by constructor; simp [LeftIdentity]; exact congrFun rfl
  add_assoc := by exact Nat.add_assoc
  add_comm := by exact Nat.add_comm
}

example: CommMonoid Nat := {
  add := Nat.mul
  zero := 1
  add_zero := ⟨Nat.one_mul, Nat.mul_one⟩
  add_assoc := by exact Nat.mul_assoc
  add_comm := by exact Nat.mul_comm
}
