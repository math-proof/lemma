/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/SpecialFunctions/KlamkinVariant.lean -/


import Lemma.Real.SpecialFunctions.KlamkinVariant
import sympy.atlas.Analysis.SpecialFunctions.GaussHypergeometricSummationKlamkin
import Lemma.Real.GaussHypergeometricSummationKlamkin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order

open MetaMathlibExt

example : HasSum (fun k : ℕ =>
    ordinaryHypergeometricCoefficient ((1 : ℕ) : ℝ) ((1 / 3 : ℝ) + 1)
      ((1 / 3 : ℝ) - (-7 / 2 : ℝ)) k)
    (Real.Gamma (-(-7 / 2 : ℝ) - ((1 : ℕ) : ℝ) - 1) *
      Real.Gamma ((1 / 3 : ℝ) - (-7 / 2 : ℝ)) /
      (Real.Gamma ((1 / 3 : ℝ) - (-7 / 2 : ℝ) - ((1 : ℕ) : ℝ)) *
        Real.Gamma (-(-7 / 2 : ℝ) - 1))) := by
  apply hasSum_ordinaryHypergeometricCoefficient_klamkin
    (n := 1) (a := (-7 / 2 : ℝ)) (b := (1 / 3 : ℝ))
  · intro m hm
    have hlow_real : (3 : ℝ) < (m : ℝ) := by
      rw [← hm]
      norm_num
    have hlow : 3 < m := by
      exact_mod_cast hlow_real
    have hhigh_real : (m : ℝ) < (4 : ℝ) := by
      rw [← hm]
      norm_num
    have hhigh : m < 4 := by
      exact_mod_cast hhigh_real
    omega
  · intro m hm
    have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    norm_num at hm
    linarith
  · norm_num
  · norm_num
  · intro m hm
    have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    norm_num at hm
    linarith

-- The concrete Abel specialization at n = 1 has a summable Gamma series.
example : Summable (fun k : ℕ =>
    (-1 : ℝ) ^ k * (Nat.choose (1 + k - 1) k : ℝ) *
      (Real.Gamma ((-7 / 2 : ℝ) + 1) /
        (Real.Gamma ((1 / 3 : ℝ) + (k : ℝ) + 1) *
          Real.Gamma ((-7 / 2 : ℝ) - ((1 / 3 : ℝ) + (k : ℝ)) + 1)))⁻¹) := by
  apply HasSum.summable
  apply variant_Klamkin
  · intro m hm
    have hlow_real : (3 : ℝ) < (m : ℝ) := by
      rw [← hm]
      norm_num
    have hlow : 3 < m := by
      exact_mod_cast hlow_real
    have hhigh_real : (m : ℝ) < (4 : ℝ) := by
      rw [← hm]
      norm_num
    have hhigh : m < 4 := by
      exact_mod_cast hhigh_real
    omega
  · intro m hm
    have hm_nonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    norm_num at hm
    linarith
  · norm_num
  · norm_num
  · intro m hm
    have hlow_real : (-4 : ℝ) < (m : ℝ) := by
      rw [← hm]
      norm_num
    have hlow : (-4 : ℤ) < m := by
      exact_mod_cast hlow_real
    have hhigh_real : (m : ℝ) < (-3 : ℝ) := by
      rw [← hm]
      norm_num
    have hhigh : m < (-3 : ℤ) := by
      exact_mod_cast hhigh_real
    omega
