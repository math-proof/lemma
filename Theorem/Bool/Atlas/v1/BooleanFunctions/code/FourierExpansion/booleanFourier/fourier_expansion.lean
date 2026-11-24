module
public import Mathlib
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.FourierExpansion.booleanFourier.sum_chi_mul_chi
open Finset BigOperators BooleanFourier Bool


public section

/--
[fourier_expansion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/FourierExpansion.lean)
-/
@[path]
private theorem main
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {x : Fin n → Bool} :
-- imply
  f x = ∑ S : Finset (Fin n), fourierCoeff f S * chi S x := by
-- proof
  classical
  have h2n : (2 : ℝ) ^ n ≠ 0 := pow_ne_zero n (by norm_num : (2 : ℝ) ≠ 0)
  simp only [BooleanFourier.fourierCoeff, one_div]
  have key : ∑ S : Finset (Fin n), (2 ^ n : ℝ)⁻¹ *
    (∑ y : Fin n → Bool, f y * chi S y) * chi S x =
    (2 ^ n : ℝ)⁻¹ * (f x * (2 : ℝ) ^ n) := by
    have step1 : ∑ S : Finset (Fin n), (2 ^ n : ℝ)⁻¹ *
      (∑ y : Fin n → Bool, f y * chi S y) * chi S x =
      (2 ^ n : ℝ)⁻¹ * ∑ S : Finset (Fin n),
        (∑ y : Fin n → Bool, f y * chi S y) * chi S x := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
    rw [step1]
    congr 1
    have step2 : ∑ S : Finset (Fin n),
      (∑ y : Fin n → Bool, f y * chi S y) * chi S x =
      ∑ S : Finset (Fin n),
        ∑ y : Fin n → Bool, f y * chi S y * chi S x := by
      congr 1; ext S; exact Finset.sum_mul Finset.univ _ _
    rw [step2, Finset.sum_comm]
    have step3 : ∑ y : Fin n → Bool,
      ∑ S : Finset (Fin n), f y * chi S y * chi S x =
      ∑ y : Fin n → Bool,
        f y * ∑ S : Finset (Fin n), chi S y * chi S x := by
      congr 1; ext y
      have : ∑ S : Finset (Fin n), f y * chi S y * chi S x =
        f y * ∑ S : Finset (Fin n), chi S y * chi S x := by
        simp_rw [show ∀ S : Finset (Fin n), f y * chi S y * chi S x =
          f y * (chi S y * chi S x) from fun S => by ring]
        rw [← Finset.mul_sum (a := f y) (s := Finset.univ)]
      exact this
    rw [step3]
    simp_rw [sum_chi_mul_chi, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ x]
    simp only [Finset.mem_univ, ite_true]
  rw [key]
  field_simp


theorem BooleanFourier.fourier_expansion
  {n : ℕ}
  {f : (Fin n → Bool) → ℝ}
  {x : Fin n → Bool} :
-- imply
  f x = ∑ S : Finset (Fin n), fourierCoeff f S * chi S x := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
