/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/SquarefreeTotientWeighted.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Def.NumberTheory.PrimeCounting.SquarefreeTotient.Part2
public import Theorem.Nat.PrimeCounting.SquarefreeTotient
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.NumberTheory.AbelSummation
public import Mathlib.Tactic

@[expose] public section

namespace MathlibExt.NumberTheory.PrimeCounting

open scoped BigOperators

open Finset MeasureTheory

noncomputable def btWeightedPrefix (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Icc 0 n, c k

noncomputable def btSieveWeight (z : ℕ) (t : ℝ) : ℝ :=
  (z : ℝ) / (z + t)

noncomputable def btSieveKernel (z : ℕ) (t : ℝ) : ℝ :=
  (z : ℝ) / (z + t) ^ 2

noncomputable def btSieveAntiderivative (z : ℕ) (C t : ℝ) : ℝ :=
  -btSieveWeight z t * (Real.log t + C) + Real.log t - Real.log (z + t)

noncomputable def btMoebiusTotientTerm (q : ℕ) : ℝ :=
  (((ArithmeticFunction.moebius q : ℤ) : ℝ) ^ 2 / Nat.totient q)

end MathlibExt.NumberTheory.PrimeCounting
