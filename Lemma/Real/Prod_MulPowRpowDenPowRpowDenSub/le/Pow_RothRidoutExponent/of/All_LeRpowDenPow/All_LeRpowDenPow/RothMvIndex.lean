import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
open MathlibExt.NumberTheory.RothAuxiliary


private lemma roth_ridout_pow_exponent_eq
  {m : ℕ}
  (p : ι → ℕ)
  (r : Fin m → ℕ)
  (a b : Fin m → ι → ℕ)
  (k : RothMvIndex m)
  (l : ι) :
-- imply
  (p l : ℝ) ^ rothRidoutExponent r a b k l =
    ∏ h, ((p l : ℝ) ^ a h l) ^ k h *
      ((p l : ℝ) ^ b h l) ^ (r h - k h) := by
-- proof
  unfold rothRidoutExponent
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro h _
  rw [pow_add, pow_mul, pow_mul]

/--
[roth_ridout_den_rpow_prod_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  {m : ℕ}
  (p : ι → ℕ)
  (q : Fin m → ℚ)
  (r : Fin m → ℕ)
  (a b : Fin m → ι → ℕ)
  (μ ν : ι → ℝ)
  (k : RothMvIndex m)
  (l : ι)
-- given
  (ha : ∀ h, Real.rpow ((q h).den : ℝ) (μ l) ≤ (p l : ℝ) ^ a h l)
  (hb : ∀ h, Real.rpow ((q h).den : ℝ) (ν l) ≤ (p l : ℝ) ^ b h l) :
-- imply
  (∏ h, (Real.rpow ((q h).den : ℝ) (μ l)) ^ k h *
    (Real.rpow ((q h).den : ℝ) (ν l)) ^ (r h - k h)) ≤
      (p l : ℝ) ^ rothRidoutExponent r a b k l := by
-- proof
  rw [roth_ridout_pow_exponent_eq]
  apply Finset.prod_le_prod₀
  ·
    intro h _
    exact mul_nonneg
      (pow_nonneg (Real.rpow_nonneg (by positivity) _) _)
      (pow_nonneg (Real.rpow_nonneg (by positivity) _) _)
  ·
    intro h _
    apply mul_le_mul
    ·
      exact pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) (ha h) _
    ·
      exact pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) (hb h) _
    ·
      exact pow_nonneg (Real.rpow_nonneg (by positivity) _) _
    ·
      exact pow_nonneg (pow_nonneg (Nat.cast_nonneg _) _) _


-- created on 2026-10-21
