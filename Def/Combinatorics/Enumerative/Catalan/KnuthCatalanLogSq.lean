module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.NumberTheory.Harmonic.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Theorem.Combinatorics.Enumerative.Catalan.KnuthCatalanLogSq

@[expose] public section

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
