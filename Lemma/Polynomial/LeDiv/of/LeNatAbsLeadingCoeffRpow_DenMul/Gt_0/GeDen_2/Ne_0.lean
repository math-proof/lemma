import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.PowDen.le.NatAbsLeadingCoeff.of.Ne_0
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[roth_univariate_index_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (P : ℤ[X])
  (q : ℚ)
  (k r : ℕ)
  (δ : ℝ)
-- given
  (hdiv : (C (q.den : ℤ) * X - C q.num) ^ k ∣ P)
  (hheight : (P.leadingCoeff.natAbs : ℝ) ≤ Real.rpow (q.den : ℝ) (δ * r))
  (hr : 0 < r)
  (hq : 2 ≤ q.den)
  (hP : P ≠ 0) :
-- imply
  (k : ℝ) / r ≤ δ := by
-- proof
  have hpowNat := PowDen.le.NatAbsLeadingCoeff.of.Ne_0 P q k hdiv hP
  have hpow : Real.rpow (q.den : ℝ) k ≤ Real.rpow (q.den : ℝ) (δ * r) := calc
    _ = ((q.den ^ k : ℕ) : ℝ) := by
      rw [Real.rpow_eq_pow, Real.rpow_natCast]
      norm_cast
    _ ≤ (P.leadingCoeff.natAbs : ℝ) := by
      exact_mod_cast hpowNat
    _ ≤ Real.rpow (q.den : ℝ) (δ * r) := hheight
  apply (div_le_iff₀ (by exact_mod_cast hr : (0 : ℝ) < r)).2
  simpa [mul_comm] using
    (Real.strictMono_rpow_of_base_gt_one (by exact_mod_cast hq)).le_iff_le.mp hpow


-- created on 2026-10-21
