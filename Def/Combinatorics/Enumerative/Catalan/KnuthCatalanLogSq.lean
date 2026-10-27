import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorem.Combinatorics.Enumerative.Catalan.KnuthCatalanLogSq


section

open scoped BigOperators

namespace MetaMathlibExt

/-- Harmonic-number difference driving the log-squared coefficients. -/
noncomputable def harmDiff (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range (2 * (n + 1) - 1), ((k : ℝ) + 1)⁻¹)
    - (∑ k ∈ Finset.range (n + 1), ((k : ℝ) + 1)⁻¹)

/-- Unnormalized log-squared coefficient. -/
noncomputable def harmD (n : ℕ) : ℝ := (Nat.centralBinom (n + 1) : ℝ) * harmDiff n

end MetaMathlibExt
end
