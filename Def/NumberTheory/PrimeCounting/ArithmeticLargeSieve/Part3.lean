module
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Def.NumberTheory.PrimeCounting.WeightedLargeSieve
public import Theorem.Nat.PrimeCounting.WeightedLargeSieve
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Tactic
public import Theorem.NumberTheory.PrimeCounting.ArithmeticLargeSieve
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ArithmeticLargeSieve.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
namespace MathlibExt.NumberTheory.PrimeCounting

noncomputable def btRestrictedSieveDensity (N z q : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r q),
    ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)

noncomputable def btSquarefreeDivisorSum (q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors.filter Squarefree, (Nat.totient d : ℝ)⁻¹

end MathlibExt.NumberTheory.PrimeCounting
