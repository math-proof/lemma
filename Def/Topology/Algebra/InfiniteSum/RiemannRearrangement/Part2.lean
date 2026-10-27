import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Theorem.Topology.Algebra.InfiniteSum.RiemannRearrangement


namespace Series.RiemannRearrangementWanted

open BigOperators

/-- Nonnegative indices, enumerated in increasing order. Zeros are included here. -/
noncomputable def posEnum (f : ℕ → ℝ) : ℕ → ℕ :=
  Nat.nth (fun n => 0 ≤ f n)

/-- Negative indices, enumerated in increasing order. -/
noncomputable def negEnum (f : ℕ → ℝ) : ℕ → ℕ :=
  Nat.nth (fun n => f n < 0)

end Series.RiemannRearrangementWanted
