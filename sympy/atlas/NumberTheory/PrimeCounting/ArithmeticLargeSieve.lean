/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/ArithmeticLargeSieve.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Basic.Real.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import sympy.atlas.NumberTheory.PrimeCounting.WeightedLargeSieve
import Lemma.Nat.PrimeCounting.WeightedLargeSieve
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

open scoped BigOperators

namespace MathlibExt.NumberTheory.PrimeCounting

private def btFareyIndex (z : ℕ) :=
  {p : Fin (z + 1) × Fin (z + 1) //
    0 < p.2.1 ∧ p.1.1 < p.2.1 ∧ Nat.Coprime p.1.1 p.2.1}

private noncomputable instance (z : ℕ) : Fintype (btFareyIndex z) := by
  classical
  unfold btFareyIndex
  infer_instance

private noncomputable def btFareyPoint {z : ℕ} (p : btFareyIndex z) : ℝ :=
  (p.1.1.1 : ℝ) / p.1.2.1

private noncomputable def btFareyDelta {z : ℕ} (p : btFareyIndex z) : ℝ :=
  1 / ((p.1.2.1 : ℝ) * z)

private noncomputable def btFareyFourier {z : ℕ}
    (S : Finset ℕ) (p : btFareyIndex z) : ℂ :=
  ∑ n ∈ S, Complex.exp ((((2 * Real.pi *
    (n * btFareyPoint p) : ℝ) : ℝ) : ℂ) * Complex.I)

private noncomputable def btSieveDensity (N z : ℕ) : ℝ :=
  ∑ r ∈ Finset.Icc 1 z,
    ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)

private noncomputable def btRoot (k b : ℕ) : ℂ :=
  Complex.exp ((((2 * Real.pi * ((b : ℝ) / k) : ℝ) : ℂ) * Complex.I))

private def btFareyMk {z : ℕ} (a r : ℕ) (hr : 0 < r) (har : a < r)
    (hrz : r ≤ z) (hcop : Nat.Coprime a r) : btFareyIndex z :=
  ⟨(⟨a, by omega⟩, ⟨r, by omega⟩), hr, har, hcop⟩

@[simp] private theorem btFareyMk_num {z a r : ℕ} {hr : 0 < r} {har : a < r}
    {hrz : r ≤ z} {hcop : Nat.Coprime a r} :
    (btFareyMk a r hr har hrz hcop).1.1.1 = a := rfl

@[simp] private theorem btFareyMk_den {z a r : ℕ} {hr : 0 < r} {har : a < r}
    {hrz : r ≤ z} {hcop : Nat.Coprime a r} :
    (btFareyMk a r hr har hrz hcop).1.2.1 = r := rfl

private noncomputable def btRestrictedSieveDensity (N z q : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Icc 1 z).filter (fun r ↦ Nat.Coprime r q),
    ((N : ℝ) + 3 * (r : ℝ) * z / 2)⁻¹ *
      (((ArithmeticFunction.moebius r : ℤ) : ℝ) ^ 2 / Nat.totient r)

private noncomputable def btSquarefreeDivisorSum (q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors.filter Squarefree, (Nat.totient d : ℝ)⁻¹
end MathlibExt.NumberTheory.PrimeCounting
