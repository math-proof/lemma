module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Nth
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Theorem.Topology.Algebra.InfiniteSum.RiemannRearrangement

@[expose] public section

namespace Series.RiemannRearrangementWanted

open BigOperators

/-- Nonnegative indices, enumerated in increasing order. Zeros are included here. -/
noncomputable def posEnum (f : ℕ → ℝ) : ℕ → ℕ :=
  Nat.nth (fun n => 0 ≤ f n)

/-- Negative indices, enumerated in increasing order. -/
noncomputable def negEnum (f : ℕ → ℝ) : ℕ → ℕ :=
  Nat.nth (fun n => f n < 0)

end Series.RiemannRearrangementWanted
