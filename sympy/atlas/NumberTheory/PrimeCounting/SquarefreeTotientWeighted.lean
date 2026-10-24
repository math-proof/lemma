/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/SquarefreeTotientWeighted.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import sympy.atlas.NumberTheory.PrimeCounting.SquarefreeTotient
import Lemma.Nat.PrimeCounting.SquarefreeTotient
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Tactic

namespace MathlibExt.NumberTheory.PrimeCounting

open scoped BigOperators
open Finset MeasureTheory

private noncomputable def btWeightedPrefix (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 0 n, c k

private noncomputable def btSieveWeight (z : ℕ) (t : ℝ) : ℝ :=
  (z : ℝ) / (z + t)

private noncomputable def btSieveKernel (z : ℕ) (t : ℝ) : ℝ :=
  (z : ℝ) / (z + t) ^ 2

private noncomputable def btSieveAntiderivative (z : ℕ) (C t : ℝ) : ℝ :=
  -btSieveWeight z t * (Real.log t + C) + Real.log t - Real.log (z + t)

private noncomputable def btMoebiusTotientTerm (q : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / Nat.totient q)
end MathlibExt.NumberTheory.PrimeCounting
