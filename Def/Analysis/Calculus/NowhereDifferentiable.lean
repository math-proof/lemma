import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Separation.CompletelyRegular


namespace Real.Calculus.NowhereDifferentiable

/-- The set of bounded continuous real functions admitting a point `x` in
`Set.Icc (-k) k` with global Lipschitz-at-`x` constant `n`. -/
def badSet (n k : ℕ) : Set (BoundedContinuousFunction ℝ ℝ) :=
  {f | ∃ x ∈ Set.Icc (-(k : ℝ)) (k : ℝ),
    ∀ y : ℝ, ‖f y - f x‖ ≤ (n : ℝ) * ‖y - x‖}

end Real.Calculus.NowhereDifferentiable
