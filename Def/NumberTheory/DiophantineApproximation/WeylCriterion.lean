/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DiophantineApproximation/WeylCriterion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3

Weyl's equidistribution criterion: a real sequence is equidistributed modulo 1
if and only if every nontrivial Fourier mean vanishes.
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Topology.Instances.AddCircle.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semiring
open scoped BigOperators
open Filter Topology


namespace MetaMathlibExt

/-- The exponential monomial `e h t = exp (2 * π * h * t * I)`. -/
noncomputable def wcE (h : ℤ) (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * (h : ℝ) * t : ℝ) : ℂ) * Complex.I)

/-- Count of `n < N` with `Int.fract (x n)` in `[a, b)`. -/
noncomputable def wcCnt (x : ℕ → ℝ) (a b : ℝ) (N : ℕ) : ℕ :=
  (Finset.filter (fun n => a ≤ Int.fract (x n) ∧ Int.fract (x n) < b)
    (Finset.range N)).card

/-- Trapezoidal bump below the indicator of `[a, b)`. -/
noncomputable def wcPhi (a b δ t : ℝ) : ℝ :=
  max 0 (min 1 (min ((t - a) / δ) ((b - t) / δ)))

end MetaMathlibExt
