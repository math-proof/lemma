import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Algebra.InfiniteSum.Real


namespace Series.RiemannRearrangementWanted

open BigOperators

/-- Ordinary ordered convergence via ordered partial sums:
`Tendsto (fun N => ∑ n ∈ Finset.range N, f n) atTop (nhds a)`. -/
def OrderedHasSum (f : ℕ → ℝ) (a : ℝ) : Prop :=
  Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, f n) Filter.atTop (nhds a)

end Series.RiemannRearrangementWanted
