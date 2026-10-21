import Mathlib
import sympy.Basic


/--
[roth_absorb_height](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (q H C k r A : ℕ)
  (δ lam : ℝ)
-- given
  (hq : 2 ≤ q)
  (hlam : 0 ≤ lam)
  (hbase : (2 : ℝ) ≤ Real.rpow q lam)
  (hH : (H : ℝ) ≤ Real.rpow q (δ * r))
  (hC : C ≤ A * k * r) :
-- imply
  ((2 ^ C * H ^ k : ℕ) : ℝ) ≤
    Real.rpow q ((δ + lam * A) * k * r) := by
-- proof
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hq)
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (le_trans (by norm_num) hq)
  have htwo : ((2 ^ C : ℕ) : ℝ) ≤ Real.rpow q (lam * C) := calc
    _ = (2 : ℝ) ^ C := by norm_cast
    _ ≤ (Real.rpow q lam) ^ C := by gcongr
    _ = Real.rpow q (lam * C) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul hq0.le lam C).symm
  have hHpow : ((H ^ k : ℕ) : ℝ) ≤ Real.rpow q ((δ * r) * k) := calc
    _ = (H : ℝ) ^ k := by norm_cast
    _ ≤ (Real.rpow q (δ * r)) ^ k := by gcongr
    _ = Real.rpow q ((δ * r) * k) := by
      rw [← Real.rpow_natCast]
      exact (Real.rpow_mul hq0.le (δ * r) k).symm
  rw [Nat.cast_mul]
  calc
    _ ≤ Real.rpow q (lam * C) * Real.rpow q ((δ * r) * k) :=
      mul_le_mul htwo hHpow (by positivity) (Real.rpow_nonneg hq0.le _)
    _ = Real.rpow q (lam * C + (δ * r) * k) :=
      (Real.rpow_add hq0 _ _).symm
    _ ≤ Real.rpow q ((δ + lam * A) * k * r) := by
      apply Real.rpow_le_rpow_of_exponent_le hq1
      have hCReal : (C : ℝ) ≤ A * k * r := by exact_mod_cast hC
      nlinarith


-- created on 2026-10-21
