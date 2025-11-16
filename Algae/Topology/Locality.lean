
import Algae.GroupTheory.Action
import Algae.Topology.MetricSpace

/-

Locality principle.

- Let X, S, T, D be sets.
- Let d be a metric on X with values in D.
- Let f be an action of T on (X → S).
- Let s be an action of T on D.

The map f satisfies a locality principle with speed c ∈ D
if for all u, v: X → S, for all x, if u(x) = v(x) for all
x in a ball of radius c*t, then f(u, t) = f(v, t) at x.

-/
variable {X S T D: Type} [DistanceSpace D] [Monoid T]

def Locality (d: Metric X D) (f: Action (X → S) T) [Action D T] (c: D): Prop :=
  ∀ (x₀: X) (t: T) (u v: X → S),
  (∀ z, z ∈ OpenBall d x₀ (c • t) → u z = v z) → (u • t) x₀ = (v • t) x₀

example (d: Metric X D) (f: Action (X → S) T) [Action D T] (c: D) (h: Locality d f ⊥) (hd: ∀ t: T, (⊥: D) • t = (⊥: D)): ∀ (u v: X → S) (t: T), u • t = v • t := by
  intro u v t
  ext x₀
  apply h x₀ t u v
  rw [hd t]
  intro z hz
  have: OpenBall d x₀ ⊥ = Set.empty := by sorry
  rw [this] at hz
  contradiction
