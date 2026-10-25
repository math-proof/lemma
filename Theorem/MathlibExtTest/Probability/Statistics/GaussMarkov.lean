/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Probability/Statistics/GaussMarkov.lean -/


import Lemma.Measure.Statistics.GaussMarkov
open Matrix MathlibExt.Probability.Statistics.GaussMarkov

/-!
# Tests for Gauss–Markov covariance minimality

Authors: Muse Spark 1.3
-/


/-- The `1 × 1` identity design matrix satisfies the invertibility hypothesis. -/
example : IsUnit ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1) := by
  simp

/-- At `X = 1`, the least-squares matrix is a left inverse of `X`. -/
example : (((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1)⁻¹ *
    (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ) * 1 = 1 := by
  have hX : IsUnit ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1) := by
    simp
  obtain ⟨hB, -⟩ := gaussMarkov_covariance_minimality 1 hX
  exact hB

/-- At `X = 1`, every competing left inverse has covariance at least the least-squares one. -/
example (A : Matrix (Fin 1) (Fin 1) ℝ)
    (hA : A * (1 : Matrix (Fin 1) (Fin 1) ℝ) = 1) :
    (A * Aᵀ - (((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1)⁻¹ *
      (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ) *
      ((((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1)⁻¹ *
        (1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ))ᵀ).PosSemidef := by
  have hX : IsUnit ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ * 1) := by
    simp
  obtain ⟨-, hmin⟩ := gaussMarkov_covariance_minimality 1 hX
  exact hmin A hA

