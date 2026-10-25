/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/KKLfromHC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.VectorTwoPoint
import Theorem.StatisticalMechanics.Code.Probability.KKLInequality.Part4
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Def.StatisticalMechanics.Code.Probability.KKLfromHC.Part3
open scoped BigOperators
open Finset

set_option linter.style.longLine false


namespace StatMech

namespace Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


theorem khc_fourier_expansion (f : (ι → Bool) → ℝ) (x : ι → Bool) :
    (∑ S : Finset ι, khc_fourierCoeff f S * khc_walshChar S x) = f x := by
  calc (∑ S : Finset ι, khc_fourierCoeff f S * khc_walshChar S x)
      = ∑ S : Finset ι, (∑ y : ι → Bool, f y * khc_walshChar S y) / (2 ^ Fintype.card ι)
          * khc_walshChar S x := by
        unfold khc_fourierCoeff bnt_uexp; rfl
    _ = (∑ S : Finset ι, ∑ y : ι → Bool, f y * khc_walshChar S y * khc_walshChar S x)
          / (2 ^ Fintype.card ι) := by
        rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro S _
        rw [div_mul_eq_mul_div, Finset.sum_mul]
    _ = (∑ y : ι → Bool, f y * (∑ S : Finset ι, khc_walshChar S y * khc_walshChar S x))
          / (2 ^ Fintype.card ι) := by
        rw [Finset.sum_comm]; congr 1; apply Finset.sum_congr rfl; intro y _
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro S _; ring
    _ = (∑ y : ι → Bool, f y * (if y = x then (2 ^ Fintype.card ι : ℝ) else 0))
          / (2 ^ Fintype.card ι) := by
        congr 1; apply Finset.sum_congr rfl; intro y _; rw [khc_sum_walshChar_mul]
    _ = f x := by
        rw [Finset.sum_eq_single x]
        · rw [if_pos rfl, mul_div_assoc, div_self (by positivity), mul_one]
        · intro y _ hy; rw [if_neg hy, mul_zero]
        · intro h; exact absurd (Finset.mem_univ x) h


theorem khc_uexp_finset_sum {κ : Type*} (s : Finset κ) (g : κ → (ι → Bool) → ℝ) :
    bnt_uexp (fun x => ∑ k ∈ s, g k x) = ∑ k ∈ s, bnt_uexp (g k) := by
  unfold bnt_uexp; simp_rw [Finset.sum_div]; rw [Finset.sum_comm]


theorem khc_uexp_const_mul (c : ℝ) (g : (ι → Bool) → ℝ) :
    bnt_uexp (fun x => c * g x) = c * bnt_uexp g := by
  unfold bnt_uexp; rw [← Finset.mul_sum, mul_div_assoc]


theorem khc_uexp_fourier_mul (a b : Finset ι → ℝ) :
    bnt_uexp (fun x => (∑ S : Finset ι, a S * khc_walshChar S x)
        * (∑ T : Finset ι, b T * khc_walshChar T x))
      = ∑ S : Finset ι, a S * b S := by
  have hexp : (fun x => (∑ S : Finset ι, a S * khc_walshChar S x)
        * (∑ T : Finset ι, b T * khc_walshChar T x))
      = (fun x => ∑ S : Finset ι, ∑ T : Finset ι,
          (a S * b T) * (khc_walshChar S x * khc_walshChar T x)) := by
    funext x; rw [Finset.sum_mul_sum]; apply Finset.sum_congr rfl; intro S _
    apply Finset.sum_congr rfl; intro T _; ring
  rw [hexp, khc_uexp_finset_sum]
  apply Finset.sum_congr rfl; intro S _
  rw [khc_uexp_finset_sum]
  have hterm : ∀ T : Finset ι,
      bnt_uexp (fun x => a S * b T * (khc_walshChar S x * khc_walshChar T x))
        = a S * b T * (if S = T then 1 else 0) := by
    intro T
    rw [khc_uexp_const_mul (a S * b T) (fun x => khc_walshChar S x * khc_walshChar T x),
        khc_orthonormal]
  simp_rw [hterm]
  rw [Finset.sum_eq_single S]
  · rw [if_pos rfl, mul_one]
  · intro T _ hT; rw [if_neg (Ne.symm hT), mul_zero]
  · intro h; exact absurd (Finset.mem_univ S) h


theorem khc_parseval (f g : (ι → Bool) → ℝ) :
    bnt_uexp (fun x => f x * g x)
      = ∑ S : Finset ι, khc_fourierCoeff f S * khc_fourierCoeff g S := by
  have hf : (fun x => f x * g x)
      = (fun x => (∑ S : Finset ι, khc_fourierCoeff f S * khc_walshChar S x)
          * (∑ T : Finset ι, khc_fourierCoeff g T * khc_walshChar T x)) := by
    funext x; rw [khc_fourier_expansion, khc_fourier_expansion]
  rw [hf, khc_uexp_fourier_mul]


theorem khc_parseval_sq (f : (ι → Bool) → ℝ) :
    bnt_uexp (fun x => (f x) ^ 2) = ∑ S : Finset ι, (khc_fourierCoeff f S) ^ 2 := by
  have h := khc_parseval f f
  simp_rw [← sq] at h
  exact h


theorem khc_noiseOp_walshChar_apply (ρ : ℝ) (S : Finset ι) (x : ι → Bool) :
    bnt_noiseOp ρ (khc_walshChar S) x = ρ ^ S.card * khc_walshChar S x := by
  unfold bnt_noiseOp bnt_noiseKernel khc_walshChar
  have hchar : ∀ y : ι → Bool, (∏ i ∈ S, khc_sign (y i))
      = ∏ i : ι, (if i ∈ S then khc_sign (y i) else 1) := by
    intro y; rw [Finset.prod_ite_mem, Finset.univ_inter]
  simp_rw [hchar]
  have hcomb : ∀ y : ι → Bool,
      (∏ i : ι, (if x i = y i then (1 + ρ) / 2 else (1 - ρ) / 2))
        * (∏ i : ι, (if i ∈ S then khc_sign (y i) else 1))
      = ∏ i : ι, ((if x i = y i then (1 + ρ) / 2 else (1 - ρ) / 2)
                  * (if i ∈ S then khc_sign (y i) else 1)) := by
    intro y; rw [← Finset.prod_mul_distrib]
  simp_rw [hcomb]
  rw [← Fintype.prod_sum (fun (i : ι) (c : Bool) =>
        (if x i = c then (1 + ρ) / 2 else (1 - ρ) / 2) * (if i ∈ S then khc_sign c else 1))]
  have hfac : ∀ i : ι,
      (∑ c : Bool, (if x i = c then (1 + ρ) / 2 else (1 - ρ) / 2) * (if i ∈ S then khc_sign c else 1))
        = (if i ∈ S then ρ * khc_sign (x i) else 1) := by
    intro i
    by_cases hi : i ∈ S
    · simp only [hi, if_true]; rw [Fintype.sum_bool]; cases (x i) <;> simp [khc_sign] <;> ring
    · simp only [hi, if_false, mul_one]; rw [Fintype.sum_bool]; cases (x i) <;> simp <;> ring
  simp_rw [hfac]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_ite_mem, Finset.univ_inter,
      Finset.prod_mul_distrib, Finset.prod_const]


theorem khc_noiseOp_walshChar (ρ : ℝ) (S : Finset ι) :
    bnt_noiseOp ρ (khc_walshChar S) = fun x => ρ ^ S.card * khc_walshChar S x := by
  funext x; exact khc_noiseOp_walshChar_apply ρ S x


theorem khc_noiseOp_finset_sum {κ : Type*} (ρ : ℝ) (s : Finset κ) (g : κ → (ι → Bool) → ℝ) :
    bnt_noiseOp ρ (fun x => ∑ k ∈ s, g k x) = fun x => ∑ k ∈ s, bnt_noiseOp ρ (g k) x := by
  funext x; unfold bnt_noiseOp; simp_rw [Finset.mul_sum]; rw [Finset.sum_comm]


theorem khc_noiseOp_const_mul (ρ c : ℝ) (g : (ι → Bool) → ℝ) :
    bnt_noiseOp ρ (fun x => c * g x) = fun x => c * bnt_noiseOp ρ g x := by
  funext x; unfold bnt_noiseOp; rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro y _; ring


theorem khc_noiseOp_fourier (ρ : ℝ) (f : (ι → Bool) → ℝ) :
    bnt_noiseOp ρ f
      = fun x => ∑ S : Finset ι, (ρ ^ S.card * khc_fourierCoeff f S) * khc_walshChar S x := by
  have hf : f = (fun x => ∑ S : Finset ι, khc_fourierCoeff f S * khc_walshChar S x) := by
    funext x; rw [khc_fourier_expansion]
  conv_lhs => rw [hf]
  rw [khc_noiseOp_finset_sum]
  funext x
  simp_rw [khc_noiseOp_const_mul ρ (khc_fourierCoeff f _) (khc_walshChar _)]
  apply Finset.sum_congr rfl
  intro S _
  rw [khc_noiseOp_walshChar_apply]
  ring


theorem khc_noiseOp_l2sq (ρ : ℝ) (f : (ι → Bool) → ℝ) :
    bnt_uexp (fun x => (bnt_noiseOp ρ f x) ^ 2)
      = ∑ S : Finset ι, (ρ ^ S.card) ^ 2 * (khc_fourierCoeff f S) ^ 2 := by
  rw [khc_noiseOp_fourier]
  have h := khc_uexp_fourier_mul (fun S => ρ ^ S.card * khc_fourierCoeff f S)
      (fun S => ρ ^ S.card * khc_fourierCoeff f S)
  simp_rw [← sq] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro S _; ring


end Probability
end StatMech
