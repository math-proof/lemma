/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanConvergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanBucketCancellation.Part2
import Theorem.StatisticalMechanics.Code.Onsager.KWSpectral.Part2
import Def.StatisticalMechanics.Code.Onsager.ShermanConvergence


namespace StatMech.Onsager

open Matrix BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem ons_sum_factorMajorant_length (q : ℝ) (m : ℕ) :
    (∑ f : Fin m → E, ons_factorMajorant q (List.ofFn f)) =
      if m < 2 then 0
      else (Fintype.card E : ℝ) ^ m * q ^ (m - 1) := by
  simp [ons_factorMajorant]

theorem factorMajorant_tail (q : ℝ) (n : ℕ) :
    (Fintype.card E : ℝ) ^ (n + 2) * q ^ (n + 2 - 1) =
      (Fintype.card E : ℝ) ^ 2 * q *
        ((Fintype.card E : ℝ) * q) ^ n := by
  rw [show n + 2 - 1 = n + 1 by omega]
  ring

theorem ons_summable_factorMajorant (q : ℝ) (hq : 0 ≤ q)
    (hsmall : (Fintype.card E : ℝ) * q < 1) :
    Summable (ons_factorMajorant q : List E → ℝ) := by
  let C : ℝ := Fintype.card E
  have hC : 0 ≤ C := by positivity
  have hCq : ‖C * q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC hq)]
    exact hsmall
  have hgeo : Summable fun n : ℕ => (C * q) ^ n :=
    summable_geometric_of_norm_lt_one hCq
  let J : ℕ → ℝ := fun m =>
    if m < 2 then 0 else C ^ m * q ^ (m - 1)
  have htail : Summable fun n => J (n + 2) := by
    have hmul := hgeo.mul_left (C ^ 2 * q)
    apply hmul.congr
    intro n
    simp only [J, if_neg (by omega : ¬ n + 2 < 2)]
    exact (factorMajorant_tail (E := E) q n).symm
  have hJ : Summable J := (summable_nat_add_iff 2).mp htail
  let equiv : (Sigma fun m : ℕ => Fin m → E) ≃ List E :=
    (List.equivSigmaTuple : List E ≃ Sigma fun m : ℕ => Fin m → E).symm
  apply equiv.summable_iff.mp
  rw [summable_sigma_of_nonneg]
  constructor
  · intro m
    exact (hasSum_fintype _).summable
  · change Summable fun m => ∑' f : Fin m → E,
        ons_factorMajorant q (List.ofFn f)
    have hfun : (fun m => ∑' f : Fin m → E,
        ons_factorMajorant q (List.ofFn f)) = J := by
      funext m
      rw [tsum_fintype, ons_sum_factorMajorant_length]
    rw [hfun]
    exact hJ
  intro p
  change 0 ≤ ons_factorMajorant q (List.ofFn p.2)
  unfold ons_factorMajorant
  split_ifs
  · rfl
  · exact pow_nonneg hq _

theorem ons_tsum_factorMajorant (q : ℝ) (hq : 0 ≤ q)
    (hsmall : (Fintype.card E : ℝ) * q < 1) :
    (∑' s : List E, ons_factorMajorant q s) =
      (Fintype.card E : ℝ) ^ 2 * q /
        (1 - (Fintype.card E : ℝ) * q) := by
  let C : ℝ := Fintype.card E
  have hC : 0 ≤ C := by positivity
  have hCq : ‖C * q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC hq)]
    exact hsmall
  have hmajor := ons_summable_factorMajorant (E := E) q hq hsmall
  let equiv : (Sigma fun m : ℕ => Fin m → E) ≃ List E :=
    (List.equivSigmaTuple : List E ≃ Sigma fun m : ℕ => Fin m → E).symm
  have hsigma : Summable (ons_factorMajorant q ∘ equiv) :=
    equiv.summable_iff.mpr hmajor
  let J : ℕ → ℝ := fun m =>
    if m < 2 then 0 else C ^ m * q ^ (m - 1)
  have hJ : Summable J := by
    have hs := hsigma.sigma
    have hfun : (fun m => ∑' f : Fin m → E,
        ons_factorMajorant q (List.ofFn f)) = J := by
      funext m
      rw [tsum_fintype, ons_sum_factorMajorant_length]
    change Summable fun m => ∑' f : Fin m → E,
      ons_factorMajorant q (List.ofFn f) at hs
    rw [hfun] at hs
    exact hs
  have hprefix : ∑ i ∈ Finset.range 2, J i = 0 := by
    rw [show Finset.range 2 = {0, 1} by decide]
    simp [J]
  calc
    (∑' s : List E, ons_factorMajorant q s) =
        ∑' p : Sigma fun m : ℕ => Fin m → E,
          ons_factorMajorant q (equiv p) := by
            exact (equiv.tsum_eq (ons_factorMajorant q)).symm
    _ = ∑' m : ℕ, ∑' f : Fin m → E,
          ons_factorMajorant q (List.ofFn f) := by
            simpa only [equiv, List.equivSigmaTuple_symm_apply,
              Function.comp_apply] using hsigma.tsum_sigma
    _ = ∑' m : ℕ, J m := by
          apply tsum_congr
          intro m
          rw [tsum_fintype, ons_sum_factorMajorant_length]
    _ = ∑' n : ℕ, J (n + 2) := by
          have htail := hJ.sum_add_tsum_nat_add 2
          rw [hprefix, zero_add] at htail
          exact htail.symm
    _ = ∑' n : ℕ, C ^ 2 * q * (C * q) ^ n := by
          apply tsum_congr
          intro n
          simp only [J, if_neg (by omega : ¬ n + 2 < 2)]
          exact factorMajorant_tail (E := E) q n
    _ = C ^ 2 * q * (1 - C * q)⁻¹ := by
          rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hCq]
    _ = _ := by simp only [C, div_eq_mul_inv]

theorem norm_ons_edgeWeight_le_pow (Lambda : Matrix E E ℂ) (q : ℝ)
    (hq : 0 ≤ q) (hentry : ∀ i j, ‖Lambda i j‖ ≤ q) (s : List E) :
    ‖ons_edgeWeight Lambda s‖ ≤ q ^ (s.length - 1) := by
  induction s with
  | nil => simp
  | cons a s ih =>
      cases s with
      | nil => simp
      | cons b t =>
          rw [ons_edgeWeight_cons_cons, norm_mul]
          have hmul := mul_le_mul (hentry a b) ih (norm_nonneg _) hq
          simpa [pow_succ'] using hmul

theorem norm_ons_firstReturnWeight_le_majorant
    (Lambda : Matrix E E ℂ) (e r : E) (q : ℝ)
    (hq : 0 ≤ q) (hentry : ∀ i j, ‖Lambda i j‖ ≤ q) (s : List E) :
    ‖ons_firstReturnWeight Lambda e r s‖ ≤ ons_factorMajorant q s := by
  classical
  by_cases hvalid : ons_isFirstReturnSegment e s ∧ ∀ x ∈ s, x ≠ r
  · simp only [ons_firstReturnWeight, if_pos hvalid]
    have hlen : ¬ s.length < 2 := by
      obtain ⟨interior, hform, _⟩ := hvalid.1
      rw [hform]
      simp
    rw [ons_factorMajorant, if_neg hlen]
    exact norm_ons_edgeWeight_le_pow Lambda q hq hentry s
  · simp only [ons_firstReturnWeight, if_neg hvalid, norm_zero]
    unfold ons_factorMajorant
    split_ifs
    · rfl
    · exact pow_nonneg hq _

theorem ons_firstReturnWeight_converges
    (Lambda : Matrix E E ℂ) (e r : E) (q : ℝ)
    (hq : 0 ≤ q) (hentry : ∀ i j, ‖Lambda i j‖ ≤ q)
    (hcard : (Fintype.card E : ℝ) * q < 1) :
    Summable fun s => ‖ons_firstReturnWeight Lambda e r s‖ := by
  exact (ons_summable_factorMajorant (E := E) q hq hcard).of_nonneg_of_le
    (fun s => norm_nonneg _) (norm_ons_firstReturnWeight_le_majorant Lambda e r q hq hentry)

theorem ons_tsum_norm_firstReturnWeight_le
    (Lambda : Matrix E E ℂ) (e r : E) (q : ℝ)
    (hq : 0 ≤ q) (hentry : ∀ i j, ‖Lambda i j‖ ≤ q)
    (hcard : (Fintype.card E : ℝ) * q < 1) :
    (∑' s, ‖ons_firstReturnWeight Lambda e r s‖) ≤
      (Fintype.card E : ℝ) ^ 2 * q /
        (1 - (Fintype.card E : ℝ) * q) := by
  have hweights :=
    ons_firstReturnWeight_converges Lambda e r q hq hentry hcard
  have hmajor := ons_summable_factorMajorant (E := E) q hq hcard
  calc
    (∑' s, ‖ons_firstReturnWeight Lambda e r s‖) ≤
        ∑' s, ons_factorMajorant q s :=
      hweights.tsum_le_tsum
        (norm_ons_firstReturnWeight_le_majorant Lambda e r q hq hentry)
        hmajor
    _ = _ := ons_tsum_factorMajorant (E := E) q hq hcard


theorem ons_firstReturnWeight_small
    (Lambda : Matrix E E ℂ) (e r : E) (q : ℝ)
    (hq : 0 ≤ q) (hentry : ∀ i j, ‖Lambda i j‖ ≤ q)
    (hsmall : q < (2 * (Fintype.card E : ℝ) ^ 2)⁻¹) :
    Summable (fun s => ‖ons_firstReturnWeight Lambda e r s‖) ∧
      (∑' s, ‖ons_firstReturnWeight Lambda e r s‖) < 1 := by
  let C : ℝ := Fintype.card E
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨e⟩)
  have hden : 0 < 2 * C ^ 2 := by positivity
  have hmul : q * (2 * C ^ 2) < 1 := by
    rw [inv_eq_one_div] at hsmall
    exact (lt_div_iff₀ hden).mp hsmall
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hcard : C * q < 1 := by nlinarith [mul_nonneg hq hC0]
  have hdenom : 0 < 1 - C * q := sub_pos.mpr hcard
  have hratio : C ^ 2 * q / (1 - C * q) < 1 := by
    rw [div_lt_one hdenom]
    nlinarith [mul_nonneg hq hC0]
  have hsum := ons_firstReturnWeight_converges Lambda e r q hq hentry hcard
  refine ⟨hsum, ?_⟩
  exact lt_of_le_of_lt
    (ons_tsum_norm_firstReturnWeight_le Lambda e r q hq hentry hcard)
    hratio

theorem norm_ons_KWmat_turnRoot_entry_le (L : ℕ) (x : ℝ)
    (d2 d1 : ons_Dart L) :
    ‖ons_KWmat L (x : ℂ) ons_turnRoot d2 d1‖ ≤ ‖(x : ℂ)‖ := by
  unfold ons_KWmat
  split_ifs
  · rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (norm_ons_turnW_turnRoot_le_one d1.2 d2.2)
  · simp


end StatMech.Onsager
