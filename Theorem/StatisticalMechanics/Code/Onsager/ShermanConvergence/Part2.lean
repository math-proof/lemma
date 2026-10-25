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
import Def.StatisticalMechanics.Code.Onsager.ShermanConvergence.Part2


namespace StatMech.Onsager

open Matrix BigOperators

variable {E : Type*} [Fintype E] [DecidableEq E]

theorem ons_ShermanRadius_pos (L : ℕ) [NeZero L] :
    0 < ons_ShermanRadius L := by
  unfold ons_ShermanRadius
  positivity

theorem ons_KW_firstReturnWeight_small (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (e : ons_Dart L) :
    Summable (fun s =>
      ‖ons_firstReturnWeight (ons_KWmat L (x : ℂ) ons_turnRoot)
        e (ons_dartRev L e) s‖) ∧
      (∑' s, ‖ons_firstReturnWeight
        (ons_KWmat L (x : ℂ) ons_turnRoot)
        e (ons_dartRev L e) s‖) < 1 := by
  apply ons_firstReturnWeight_small
    (ons_KWmat L (x : ℂ) ons_turnRoot) e (ons_dartRev L e)
    ‖(x : ℂ)‖ (norm_nonneg _)
    (norm_ons_KWmat_turnRoot_entry_le L x)
  simpa [ons_ShermanRadius, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hx.1] using hx.2

theorem norm_ons_loopWeight_le_pow (Lambda : Matrix E E ℂ) (q : ℝ)
    (hq : 0 ≤ q) (hentry : ∀ i j, ‖Lambda i j‖ ≤ q)
    {n : ℕ} [NeZero n] (v : Fin n → E) :
    ‖ons_loopWeight Lambda v‖ ≤ q ^ n := by
  unfold ons_loopWeight
  rw [norm_prod]
  calc
    (∏ k : Fin n, ‖Lambda (v k) (v (k + 1))‖) ≤
        ∏ _k : Fin n, q := by
      apply Finset.prod_le_prod
      · intro k _
        exact norm_nonneg _
      · intro k _
        exact hentry _ _
    _ = q ^ n := by simp

theorem norm_filtered_loopSum_le (Lambda : Matrix E E ℂ) (q : ℝ)
    (hq : 0 ≤ q) (hentry : ∀ i j, ‖Lambda i j‖ ≤ q)
    (n : ℕ) (P : (Fin (n + 1) → E) → Prop) [DecidablePred P] :
    ‖∑ v ∈ Finset.univ.filter P, ons_loopWeight Lambda v‖ ≤
      ((Fintype.card E : ℝ) * q) ^ (n + 1) := by
  calc
    ‖∑ v ∈ Finset.univ.filter P, ons_loopWeight Lambda v‖ ≤
        ∑ v ∈ Finset.univ.filter P, ‖ons_loopWeight Lambda v‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _v ∈ Finset.univ.filter P, q ^ (n + 1) := by
      apply Finset.sum_le_sum
      intro v _
      exact norm_ons_loopWeight_le_pow Lambda q hq hentry v
    _ ≤ ∑ _v : Fin (n + 1) → E, q ^ (n + 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro v _ _
      exact pow_nonneg hq _
    _ = ((Fintype.card E : ℝ) * q) ^ (n + 1) := by
      simp
      ring


theorem ons_summable_filteredLoopSeries (Lambda : Matrix E E ℂ) (q : ℝ)
    (hq : 0 ≤ q) (hentry : ∀ i j, ‖Lambda i j‖ ≤ q)
    (hcard : (Fintype.card E : ℝ) * q < 1)
    (P : (n : ℕ) → (Fin (n + 1) → E) → Prop)
    [∀ n, DecidablePred (P n)] :
    Summable fun n : ℕ =>
      (∑ v ∈ Finset.univ.filter (P n), ons_loopWeight Lambda v) /
        ((n : ℂ) + 1) := by
  classical
  have hC0 : 0 ≤ (Fintype.card E : ℝ) := by positivity
  have hgeomNorm : ‖(Fintype.card E : ℝ) * q‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC0 hq)]
    exact hcard
  have hgeom : Summable fun n : ℕ =>
      ((Fintype.card E : ℝ) * q) ^ (n + 1) :=
    (summable_nat_add_iff 1).2 (summable_geometric_of_norm_lt_one hgeomNorm)
  apply Summable.of_norm_bounded hgeom
  intro n
  calc
    ‖(∑ v ∈ Finset.univ.filter (P n), ons_loopWeight Lambda v) /
        ((n : ℂ) + 1)‖ =
        ‖∑ v ∈ Finset.univ.filter (P n), ons_loopWeight Lambda v‖ /
          (n + 1 : ℝ) := by
            rw [norm_div]
            congr 1
            rw [show (n : ℂ) + 1 = ((n + 1 : ℕ) : ℂ) by norm_num,
              norm_natCast]
            norm_num
    _ ≤ ‖∑ v ∈ Finset.univ.filter (P n), ons_loopWeight Lambda v‖ := by
      apply div_le_self (norm_nonneg _)
      norm_num
    _ ≤ _ := norm_filtered_loopSum_le Lambda q hq hentry n (P n)

theorem ons_Sherman_card_mul_small (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
    (Fintype.card (ons_Dart L) : ℝ) * ‖x‖ < 1 := by
  let C : ℝ := Fintype.card (ons_Dart L)
  have hC1 : 1 ≤ C := by
    dsimp [C]
    exact_mod_cast (Fintype.card_pos_iff.mpr
      ⟨(((0, 0), 0) : ons_Dart L)⟩)
  have hC0 : 0 ≤ C := le_trans zero_le_one hC1
  have hden : 0 < 2 * C ^ 2 := by positivity
  have hmul : x * (2 * C ^ 2) < 1 := by
    have h := hx.2
    rw [ons_ShermanRadius, inv_eq_one_div] at h
    exact (lt_div_iff₀ hden).mp h
  rw [Real.norm_eq_abs, abs_of_pos hx.1]
  nlinarith [mul_nonneg hx.1.le hC0]

theorem ons_KWmat_eq_phase_zero (L : ℕ) (x omega : ℂ) :
    ons_KWmat L x omega =
      ons_KWmatPhase L x omega (ons_spinPhase L 0) (ons_spinPhase L 0) := by
  ext d2 d1
  unfold ons_KWmatPhase
  have hphase : ons_spinPhase L 0 = 1 := by simp [ons_spinPhase]
  rw [hphase]
  generalize hmu : d1.2 = mu
  fin_cases mu <;> simp [ons_dirPhase]

theorem ons_KWmat_spectral_Sherman_small (L : ℕ) [NeZero L]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L)) :
    ∀ alpha ∈ (ons_KWmat L (x : ℂ) ons_turnRoot).charpoly.roots,
      ‖alpha‖ < 1 := by
  rw [ons_KWmat_eq_phase_zero]
  apply ons_KWmatPhase_spectral_lt_one
  exact ons_Sherman_card_mul_small L hx

theorem ons_summable_bucketN_Sherman_small
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (e : ons_Dart L) :
    Summable fun n : ℕ =>
      ons_bucketN L (x : ℂ) ons_turnRoot e n / ((n : ℂ) + 1) := by
  classical
  let P : (n : ℕ) → (Fin (n + 1) → ons_Dart L) → Prop :=
    fun _ v => ¬ (∃ i, v i = e) ∧ ¬ (∃ j, v j = ons_dartRev L e)
  have hs := ons_summable_filteredLoopSeries
    (ons_KWmat L (x : ℂ) ons_turnRoot) ‖(x : ℂ)‖ (norm_nonneg _)
    (norm_ons_KWmat_turnRoot_entry_le L x)
    (by simpa [Complex.norm_real] using ons_Sherman_card_mul_small L hx) P
  simpa only [ons_bucketN, P] using hs


theorem ons_det_eq_A_mul_firstReturn_sq_Sherman_small
    (L : ℕ) [NeZero L] [Fact (2 < L)]
    {x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) (ons_ShermanRadius L))
    (e : ons_Dart L) :
    (1 - ons_KWmat L (x : ℂ) ons_turnRoot).det =
      Complex.exp (- ∑' n : ℕ,
        ons_bucketN L (x : ℂ) ons_turnRoot e n / ((n : ℂ) + 1)) *
      (1 - ∑' s, ons_firstReturnWeight
        (ons_KWmat L (x : ℂ) ons_turnRoot)
        e (ons_dartRev L e) s) ^ 2 := by
  have hfirst := ons_KW_firstReturnWeight_small L hx e
  apply ons_det_eq_A_mul_sq (L := L) (x : ℂ) ons_turnRoot
    ons_turnRoot_sq e (ons_KWmat_spectral_Sherman_small L hx)
    (ons_summable_bucketE_firstReturn (x : ℂ) ons_turnRoot e
      hfirst.1 hfirst.2)
    (ons_summable_bucketN_Sherman_small L hx e)
    (∑' s, ons_firstReturnWeight
      (ons_KWmat L (x : ℂ) ons_turnRoot) e (ons_dartRev L e) s)
  exact ons_hlam_firstReturn (x : ℂ) ons_turnRoot e hfirst.1 hfirst.2

end StatMech.Onsager
