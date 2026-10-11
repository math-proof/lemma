import Mathlib
import sympy.Basic
import sympy.functions.special.GaussHypergeometricSummationKlamkin


/--
[GaussHypergeometricSummationKlamkin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GaussHypergeometricSummationKlamkin.lean)
-/
@[path]
private lemma gauss_hypergeometric_summation_klamkin_eq
-- given
  (n : ℕ)
  (a b : ℝ)
  (ha : ∀ k : ℕ, -a ≠ (k : ℝ))
  (hb : ∀ k : ℕ, -b ≠ (k : ℝ))
  (hn : 1 ≤ n)
  (hconv : a + 1 + n < 0)
  (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ)) :
-- imply
  ordinaryHypergeometric (n : ℝ) (b + 1) (b - a) (1 : ℝ) =
    Real.Gamma (-a - n - 1) * Real.Gamma (b - a) /
      (Real.Gamma (b - a - n) * Real.Gamma (-a - 1)) := by
-- proof
  apply MetaMathlibExt.gauss_hypergeometric_summation_klamkin n a b ha hb hn hconv hadmissible

/--
[GaussHypergeometricSummationKlamkin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/GaussHypergeometricSummationKlamkin.lean)
-/
@[path]
private lemma has_sum_ordinary_hypergeometric_coefficient_klamkin_is
-- given
  (n : ℕ)
  (a b : ℝ)
  (ha : ∀ k : ℕ, -a ≠ (k : ℝ))
  (hb : ∀ k : ℕ, -b ≠ (k : ℝ))
  (hn : 1 ≤ n)
  (hconv : a + 1 + n < 0)
  (hadmissible : ∀ k : ℕ, a - b + 1 ≠ (k : ℝ)) :
-- imply
  HasSum (fun k : ℕ => ordinaryHypergeometricCoefficient (n : ℝ) (b + 1) (b - a) k)
    (Real.Gamma (-a - n - 1) * Real.Gamma (b - a) /
      (Real.Gamma (b - a - n) * Real.Gamma (-a - 1))) := by
-- proof
  apply MetaMathlibExt.hasSum_ordinaryHypergeometricCoefficient_klamkin n a b ha hb hn hconv hadmissible


-- created on 2026-10-11
