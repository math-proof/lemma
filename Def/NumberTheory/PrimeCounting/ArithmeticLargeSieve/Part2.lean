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
import Instance.NumberTheory.PrimeCounting.ArithmeticLargeSieve
open scoped BigOperators


namespace MathlibExt.NumberTheory.PrimeCounting

noncomputable def btFareyPoint {z : ℕ} (p : btFareyIndex z) : ℝ :=
  (p.1.1.1 : ℝ) / p.1.2.1

noncomputable def btFareyDelta {z : ℕ} (p : btFareyIndex z) : ℝ :=
  1 / ((p.1.2.1 : ℝ) * z)

noncomputable def btFareyFourier {z : ℕ}
    (S : Finset ℕ) (p : btFareyIndex z) : ℂ :=
  ∑ n ∈ S, Complex.exp ((((2 * Real.pi *
    (n * btFareyPoint p) : ℝ) : ℝ) : ℂ) * Complex.I)

noncomputable def btSieveDensity (N z : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 z,
    ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)

noncomputable def btRoot (k b : ℕ) : ℂ :=
  Complex.exp ((((2 * Real.pi * ((b : ℝ) / k) : ℝ) : ℂ) * Complex.I))

def btFareyMk {z : ℕ} (a r : ℕ) (hr : 0 < r) (har : a < r)
    (hrz : r ≤ z) (hcop : Nat.Coprime a r) : btFareyIndex z :=
  ⟨(⟨a, by omega⟩, ⟨r, by omega⟩), hr, har, hcop⟩

end MathlibExt.NumberTheory.PrimeCounting
