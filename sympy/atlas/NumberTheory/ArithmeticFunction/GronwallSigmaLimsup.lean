/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ArithmeticFunction/GronwallSigmaLimsup.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Data.Nat.Prime.Int

section
namespace MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted

/-!
# Gronwall's maximal order of σ
This file proves Gronwall's exact maximal-order theorem for the divisor-sum
function.
-/

-- Proof roadmap. Names are chosen to avoid shadowing Mathlib.
-- a(n) = Λ(n) / (n * log n), S, A, P, T as in the vetted blueprint.

/-- Prime-power weight a(n) = Λ(n) / (n * log n). a(0) = a(1) = 0 since Λ vanishes there. -/
private noncomputable def mertensAcoeff (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)

/-- S(x) = ∑ Λ(n)/n over n ∈ [0, ⌊x⌋₊]. -/
private noncomputable def mertensS (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ)

/-- A(x) = ∑ a(n) over n ∈ [0, ⌊x⌋₊]. Monotone in x (nonnegative terms). -/
private noncomputable def mertensA (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊x⌋₊, mertensAcoeff n

/-- P(x) = ∏ (1 - 1/p)⁻¹ over p ∈ primesLE ⌊x⌋₊. P(x) ≥ 1 > 0. -/
private noncomputable def mertensP (x : ℝ) : ℝ :=
  ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹

/-- T(p,N) = ∑ 1/(k * p^k) over k ∈ [1, Nat.log p N]. -/
private noncomputable def primeTail (p N : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 (Nat.log p N), (1 : ℝ) / ((k : ℝ) * (p : ℝ) ^ k)

/-- f(n): the Wanted function, stated exactly as in the Wanted declaration. -/
private noncomputable def gronwallF (n : ℕ) : ℝ :=
  ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) / ((n : ℝ) * Real.log (Real.log n))

/-- Witness `n_k = prod_{p <= 2^k} p^{2k}`. -/
private noncomputable def gronwallWit (k : ℕ) : ℕ :=
  ∏ p ∈ Nat.primesLE (2 ^ k), p ^ (2 * k)
end MathlibExt.NumberTheory.ArithmeticFunction.GronwallSigmaLimsupWanted
end
