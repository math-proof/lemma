import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.DivisorClassGroup
open AlgebraicCurve


/--
[AlgebraicCurve_Divisor_exists_degZero_ord_eq_mul_of_dvd_ord](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Divisor_exists_degZero_ord_eq_mul_of_dvd_ord.lean)
-/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
  {n : ℕ}
  {f : F}
-- given
  (hn : n ≠ 0)
  (hf : f ≠ 0)
  (hdvd : ∀ v : Place K F, (n : ℤ) ∣ v.ord f) :
-- imply
  ∃ D : Divisor.degZero (K := K) (F := F), ∀ v : Place K F, v.ord f = (n : ℤ) * (D : Divisor K F) v := by
-- proof
    obtain ⟨Df, hDf, hdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) f hf
    set D0 : Divisor K F := Finsupp.mapRange (· / (n : ℤ)) (by simp) Df with hD0
    have hsmul : (n : ℤ) • D0 = Df := by
      ext v
      rw [Finsupp.smul_apply, hD0, Finsupp.mapRange_apply, smul_eq_mul]
      refine Int.mul_ediv_cancel' ?_
      rw [hDf v]
      exact hdvd v
    have hnz : (n : ℤ) ≠ 0 := Int.natCast_ne_zero.mpr hn
    have hdeg0 : D0 ∈ Divisor.degZero (K := K) (F := F) := by
      rw [Divisor.mem_degZero]
      exact (mul_eq_zero.mp (by rw [← smul_eq_mul, ← map_zsmul, hsmul, hdeg])).resolve_left hnz
    refine ⟨⟨D0, hdeg0⟩, fun v => ?_⟩
    show v.ord f = (n : ℤ) * D0 v
    rw [← hDf v, ← hsmul, Finsupp.smul_apply, smul_eq_mul]


-- created on 2026-10-23
