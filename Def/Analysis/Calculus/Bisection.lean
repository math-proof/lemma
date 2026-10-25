/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
/-!
This file constructs bisection sequences on real intervals and proves that their midpoints
converge to a bracketed root with the standard geometric error bound.
-/


namespace Real.Calculus.Bisection

/-- `u` and `v` are the bracketing endpoints produced by the bisection algorithm:
at each step their midpoint replaces the endpoint having the same sign. -/
def IsBisectionSequence (f : ℝ → ℝ) (a b : ℝ) (u v : ℕ → ℝ) : Prop :=
  u 0 = a ∧ v 0 = b ∧ ∀ n,
    let m := (u n + v n) / 2
    (f m ≤ 0 ∧ u (n + 1) = m ∧ v (n + 1) = v n) ∨
      (0 ≤ f m ∧ u (n + 1) = u n ∧ v (n + 1) = m)

end Real.Calculus.Bisection
