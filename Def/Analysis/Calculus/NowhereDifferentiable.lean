module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.GDelta.MetrizableSpace
public import Mathlib.Topology.Separation.CompletelyRegular

@[expose] public section

namespace Real.Calculus.NowhereDifferentiable

/-- The set of bounded continuous real functions admitting a point `x` in
`Set.Icc (-k) k` with global Lipschitz-at-`x` constant `n`. -/
def badSet (n k : ℕ) : Set (BoundedContinuousFunction ℝ ℝ) :=
  {f | ∃ x ∈ Set.Icc (-(k : ℝ)) (k : ℝ),
    ∀ y : ℝ, ‖f y - f x‖ ≤ (n : ℝ) * ‖y - x‖}

end Real.Calculus.NowhereDifferentiable
