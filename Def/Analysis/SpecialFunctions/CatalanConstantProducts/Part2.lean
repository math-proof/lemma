/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.Real.Pi.Leibniz
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Theorem.Analysis.SpecialFunctions.CatalanConstantProducts

@[expose] public section

section

namespace MetaMathlibExt

/-- Third product (boundary-factor form). -/
noncomputable def catR (m : ℕ) : ℝ :=
  ((∏ k ∈ Finset.range m, (4 * (k : ℝ) + 3) ^ (4 * k + 3)) /
    (∏ k ∈ Finset.range m, (4 * (k : ℝ) + 1) ^ (4 * k + 1))) ^ 2 *
  (4 * (m : ℝ) + 3) ^ (2 * m + 1) / (4 * (m : ℝ) + 1) ^ (6 * m + 1)

end MetaMathlibExt
end
