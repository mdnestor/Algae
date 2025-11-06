/-

Fibonacci numbers in a ring B)

-/

import Algae.Ring

variable {α: Type u}

def PartialSums [Monoid α] (a: Nat → α): Nat → α :=
  λ n ↦ match n with
  | 0 => unit
  | p + 1 => op (PartialSums a p) (a p)

def Fibonacci [Ring α]: Nat → α :=
  λ n ↦ match n with
  | 0 => (0: α)
  | 1 => (1: α)
  | p + 2 => Fibonacci p + Fibonacci (p + 1)

example [Ring α] (n: Nat): PartialSums (@Fibonacci α _) n = Fibonacci (n + 1) - 1 := by
  sorry

example [Ring α] (n: Nat): PartialSums (fun n => (@Fibonacci α _ n)^2) (n + 1) = Fibonacci n * Fibonacci (n + 1) := by
  sorry
