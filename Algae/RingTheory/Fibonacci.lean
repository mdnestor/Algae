import Algae.RingTheory.Ring

open Ring

variable {α: Type u}

def Magma.fibonacci [Magma α] (f₀ f₁: α): Nat → α :=
  λ n ↦ match n with
  | 0 => f₀
  | 1 => f₁
  | p + 2 => op (fibonacci f₀ f₁ p) (fibonacci f₀ f₁ (p + 1))

def Monoid.fibonacci [Monoid α] (f₁: α): Nat → α :=
  Magma.fibonacci unit f₁

def Ring.fibonacci [Ring α]: ℕ → α :=
  @Monoid.fibonacci α Ring.add_struct.toMonoid Ring.one

def PartialSum [Magma α] (a: ℕ → α) (n: ℕ): α :=
  match n with
  | 0 => a 0
  | p + 1 => op (PartialSum a p) (a (p + 1))

def PartialSum₀ [Monoid α] (a: ℕ → α) (n: ℕ): α :=
  match n with
  | 0 => unit
  | p + 1 => op (PartialSum₀ a p) (a p)

example [Monoid α] (a: ℕ → α) (n: ℕ): PartialSum a n = PartialSum₀ a (n + 1) := by
  sorry

theorem Magma.fibonacci_partial_sum [CommMonoid α] (f₀ f₁: α) (n: ℕ):
  op (PartialSum (fibonacci f₀ f₁) (n + 1)) f₁ = fibonacci f₀ f₁ (n + 3) := by
  induction n with
  | zero => simp [PartialSum, fibonacci, op_comm]
  | succ p hp => calc
    op (PartialSum (fibonacci f₀ f₁) (p + 2)) f₁
    _ = op (op (PartialSum (fibonacci f₀ f₁) (p + 1)) (fibonacci f₀ f₁ (p + 2))) f₁ := by rfl
    _ = op f₁ (op (PartialSum (fibonacci f₀ f₁) (p + 1)) (fibonacci f₀ f₁ (p + 2))) := by rw [op_comm]
    _ = op (op f₁ (PartialSum (fibonacci f₀ f₁) (p + 1))) (fibonacci f₀ f₁ (p + 2)) := by to_additive; rw [op_assoc]
    _ = op (op (PartialSum (fibonacci f₀ f₁) (p + 1)) f₁) (fibonacci f₀ f₁ (p + 2)) := by rw [op_comm f₁]
    _ = op (fibonacci f₀ f₁ (p + 3)) (fibonacci f₀ f₁ (p + 2)) := by rw [hp]
    _ = op (fibonacci f₀ f₁ (p + 2)) (fibonacci f₀ f₁ (p + 3)) := by rw [op_comm]
    _ = fibonacci f₀ f₁ (p + 4) := by rfl


def Fibonacci [Ring α]: Nat → α :=
  λ n ↦ match n with
  | 0 => (0: α)
  | 1 => (1: α)
  | p + 2 => Fibonacci p + Fibonacci (p + 1)

example [Ring α] (n: Nat): PartialSum₀ (@Fibonacci α _) n = Fibonacci (n + 1) - 1 := by
  sorry

example [Ring α] (n: Nat): PartialSum₀ (fun n => (@Fibonacci α _ n)^2) (n + 1) = Fibonacci n * Fibonacci (n + 1) := by
  sorry
