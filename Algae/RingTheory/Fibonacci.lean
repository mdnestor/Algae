import Algae.RingTheory.Ring

variable {α: Type u}

/-

Ringonacci B)

-/

section open Group

def Magma.fibonacci [Magma α] (f₀ f₁: α): Nat → α :=
  λ n ↦ match n with
  | 0 => f₀
  | 1 => f₁
  | p + 2 => fibonacci f₀ f₁ p + fibonacci f₀ f₁ (p + 1)

def Monoid.fibonacci [Monoid α] (f₁: α): Nat → α :=
  Magma.fibonacci 0 f₁

def PartialSum [Magma α] (a: Nat → α) (n: Nat): α :=
  match n with
  | 0 => a 0
  | p + 1 => PartialSum a p + a (p + 1)

def PartialSum₀ [Monoid α] (a: Nat → α) (n: Nat): α :=
  match n with
  | 0 => 0
  | p + 1 => PartialSum₀ a p + a p

example [Monoid α] (a: Nat → α) (n: Nat): PartialSum a n = PartialSum₀ a (n + 1) := by
  sorry

theorem Magma.fibonacci_partial_sum [CommMonoid α] (f₀ f₁: α) (n: Nat):
  PartialSum (fibonacci f₀ f₁) (n + 1) + f₁ = fibonacci f₀ f₁ (n + 3) := by
  induction n with
  | zero => simp [PartialSum, fibonacci, op_comm]
  | succ p hp =>
    let F := fibonacci f₀ f₁
    let σ := PartialSum F
    calc
                σ (p + 2)              + f₁
      _ =        σ (p + 1)  + F (p + 2) + f₁ := by rfl
      _ =  f₁ + (σ (p + 1)  + F (p + 2))     := by rw [op_comm]
      _ = (f₁ +  σ (p + 1)) + F (p + 2)      := by rw [op_assoc]
      _ = (σ (p + 1)  + f₁) + F (p + 2)      := by rw [op_comm f₁]
      _ =         F (p + 3) + F (p + 2)      := by rw [hp]
      _ =         F (p + 2) + F (p + 3)      := by rw [op_comm]
      _ =         F (p + 4)                  := by rfl

end

open Ring

def Ring.fibonacci [Ring α]: Nat → α :=
  @Monoid.fibonacci α Semiring.toAddMonoid.toMonoid 1

def Fibonacci [Ring α]: Nat → α :=
  λ n ↦ match n with
  | 0 => (0: α)
  | 1 => (1: α)
  | p + 2 => Fibonacci p + Fibonacci (p + 1)

example [Ring α] (n: Nat): PartialSum₀ (@Fibonacci α _) n = Fibonacci (n + 1) - 1 := by
  sorry

example [Ring α] (n: Nat): PartialSum₀ (λ n ↦ (@Fibonacci α _ n)^2) (n + 1) = Fibonacci n * Fibonacci (n + 1) := by
  sorry
