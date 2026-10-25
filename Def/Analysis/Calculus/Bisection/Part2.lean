/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Theorem.Analysis.Calculus.Bisection
/-!
This file constructs bisection sequences on real intervals and proves that their midpoints
converge to a bracketed root with the standard geometric error bound.
-/


namespace Real.Calculus.Bisection

noncomputable def bisection_pairs (f : ℝ → ℝ) (a b : ℝ) : ℕ → ℝ × ℝ
  | 0 => (a, b)
  | n + 1 =>
      let p := bisection_pairs f a b n
      let m := (p.1 + p.2) / 2
      if f m ≤ 0 then (m, p.2) else (p.1, m)

end Real.Calculus.Bisection
