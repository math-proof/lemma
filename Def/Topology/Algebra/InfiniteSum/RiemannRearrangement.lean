module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.Nth
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace Series.RiemannRearrangementWanted

open BigOperators

/-- Ordinary ordered convergence via ordered partial sums:
`Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (nhds a)`. -/
def OrderedHasSum (f : ℕ → ℝ) (a : ℝ) : Prop :=
  Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, f n) Filter.atTop (nhds a)

end Series.RiemannRearrangementWanted
