/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ArithmeticLargeSieve.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Def.NumberTheory.PrimeCounting.WeightedLargeSieve
import Lemma.Nat.PrimeCounting.WeightedLargeSieve
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic
import Theorem.NumberTheory.PrimeCounting.ArithmeticLargeSieve
open scoped BigOperators


namespace MathlibExt.NumberTheory.PrimeCounting

noncomputable def btRestrictedSieveDensity (N z q : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r q),
    ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)

noncomputable def btSquarefreeDivisorSum (q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors.filter Squarefree, (Nat.totient d : ℝ)⁻¹

end MathlibExt.NumberTheory.PrimeCounting
