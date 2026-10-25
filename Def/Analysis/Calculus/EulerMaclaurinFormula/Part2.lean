/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.NumberTheory.Bernoulli
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Analysis.Calculus.EulerMaclaurinFormula
open scoped BigOperators

/-!
# Euler-Maclaurin formula
-/


namespace Real.Calculus.EulerMaclaurinFormula

/-- Bernoulli kernel on the unit interval starting at `c`: `B_m(x - c) / m!`. -/
noncomputable def emKernel (c : ℤ) (m : ℕ) (x : ℝ) : ℝ :=
  bernoulliFun m (x - (c : ℝ)) / (Nat.factorial m : ℝ)

end Real.Calculus.EulerMaclaurinFormula
