import Mathlib
import sympy.Basic
import Lemma.ModularCurve.PhiGen
import Lemma.Int.P2MUtil

open ModularCurve Polynomial

/--
[ModularCurve_coeff_coeff_swapBivar](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_coeff_coeff_swapBivar.lean)
-/

private lemma  swapBivar_monomial (n : ℕ) (c : Polynomial ℤ) :
  swapBivar (Polynomial.monomial n c) = swapInner c * Polynomial.C Polynomial.X ^ n := by
  show (Polynomial.eval₂RingHom swapInner (Polynomial.C Polynomial.X))
    (Polynomial.monomial n c) = _
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial]

private lemma  coeff_swapInner (c : Polynomial ℤ) (j : ℕ) :
  (swapInner c).coeff j = Polynomial.C (c.coeff j) := by
  show ((Polynomial.aeval (R := ℤ)
      (Polynomial.X : Polynomial (Polynomial ℤ))) c).coeff j = _
  induction c using Polynomial.induction_on' with
  | add a b ha hb => simp only [map_add, Polynomial.coeff_add, ha, hb, map_add]
  | monomial m d =>
      simp only [Polynomial.aeval_monomial, Polynomial.coeff_monomial]
      rw [show (algebraMap ℤ (Polynomial (Polynomial ℤ))) d = Polynomial.C (Polynomial.C d) from rfl,
        Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
      by_cases h : m = j
      ·
        subst h
        simp
      · simp [h, Ne.symm h]
@[path]
private lemma main
  {Φ : Polynomial (Polynomial ℤ)}
  {i j : ℕ} :
-- imply
  ((swapBivar Φ).coeff j).coeff i = (Φ.coeff i).coeff j := by
-- proof
  induction Φ using Polynomial.induction_on' with
    | add f g hf hg =>
        simp only [map_add, Polynomial.coeff_add, hf, hg]
    | monomial n c =>
        rw [swapBivar_monomial, ← Polynomial.C_pow, mul_comm,
          Polynomial.coeff_C_mul, coeff_swapInner,
          mul_comm, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
          Polynomial.coeff_monomial]
        rcases eq_or_ne n i with rfl | h
        · simp
        · simp [h, Ne.symm h]


-- created on 2026-10-23
