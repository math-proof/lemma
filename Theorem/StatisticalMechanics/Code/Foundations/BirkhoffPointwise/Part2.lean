/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.MaximalErgodicGarsia
import Def.StatisticalMechanics.Code.Foundations.BirkhoffPointwise.Part2
open MeasureTheory Filter Finset Function MeasurableSpace
open scoped Topology ENNReal


namespace StatMech

namespace BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}


omit [MeasurableSpace α] in

theorem fStar_comp (x : α) : fStar T f (T x) = fStar T f x :=
  le_antisymm (limsup_avg_comp_le x) (limsup_avg_le_comp x)

omit [MeasurableSpace α] in

theorem coe_avg_neg (x : α) (n : ℕ) :
    ((birkhoffAverage ℝ T (-f) n x : ℝ) : EReal) = -((birkhoffAverage ℝ T f n x : ℝ) : EReal) := by
  rw [show (birkhoffAverage ℝ T (-f) n x : ℝ) = -(birkhoffAverage ℝ T f n x : ℝ) by
    rw [birkhoffAverage_neg]; rfl, EReal.coe_neg]

omit [MeasurableSpace α] in

theorem fStarLow_eq_neg_fStar_neg (x : α) : fStarLow T f x = -fStar T (-f) x := by
  unfold fStarLow fStar
  rw [← EReal.liminf_neg]
  refine liminf_congr ?_
  filter_upwards with n
  rw [Pi.neg_apply, coe_avg_neg, neg_neg]

omit [MeasurableSpace α] in

theorem fStarLow_comp (x : α) : fStarLow T f (T x) = fStarLow T f x := by
  rw [fStarLow_eq_neg_fStar_neg, fStarLow_eq_neg_fStar_neg, fStar_comp]


open StatMech.GarsiaMax in


theorem setIntegral_nonneg_of_invariant (hT : MeasurePreserving T μ μ) {g : α → ℝ}
    (hg : Integrable g μ) {E : Set α} (hEmeas : NullMeasurableSet E μ) (hEinv : IsInvariantSet T E)
    (hpos : ∀ x ∈ E, ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T g n x) :
    0 ≤ ∫ x in E, g x ∂μ := by
  
  have hgE : Integrable (E.indicator g) μ := hg.indicator₀ hEmeas
  
  set s : ℕ → Set α := fun N => {x | 0 < maxPartialSum T (E.indicator g) (N + 1) N.succ_pos x}
    with hs_def
  
  have hs_eq : ∀ N, s N = E ∩ {x | 0 < maxPartialSum T g (N + 1) N.succ_pos x} := by
    intro N
    exact setOf_maxPartialSum_indicator hEinv g N.succ_pos
  
  have hM_int : ∀ N : ℕ, Integrable
      (fun x => maxPartialSum T (E.indicator g) (N + 1) N.succ_pos x) μ :=
    fun N => integrable_maxPartialSum hT hgE N.succ_pos
  have hs_meas : ∀ N, NullMeasurableSet (s N) μ := fun N =>
    nullMeasurableSet_lt aemeasurable_const (hM_int N).aestronglyMeasurable.aemeasurable
  
  have hs_subE : ∀ N, s N ⊆ E := by
    intro N
    rw [hs_eq N]; exact Set.inter_subset_left
  
  have hs_mono : Monotone s := by
    intro N M hNM x hx
    simp only [hs_def, Set.mem_setOf_eq] at hx ⊢
    exact lt_of_lt_of_le hx
      (maxPartialSum_mono (E.indicator g) N.succ_pos M.succ_pos (Nat.succ_le_succ hNM) x)
  
  have hs_union : (⋃ N, s N) = E := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset hs_subE
    · intro x hxE
      obtain ⟨n, hn1, hnpos⟩ := hpos x hxE
      refine Set.mem_iUnion.mpr ⟨n - 1, ?_⟩
      rw [hs_eq]
      refine ⟨hxE, ?_⟩
      simp only [Set.mem_setOf_eq]
      
      have heq : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos hn1
      have hle : birkhoffSum T g n x ≤ maxPartialSum T g (n - 1 + 1) (n - 1).succ_pos x :=
        birkhoffSum_le_maxPartialSum (n - 1).succ_pos hn1 (by omega) x
      exact lt_of_lt_of_le hnpos hle
  
  have hgarsia : ∀ N, 0 ≤ ∫ x in s N, g x ∂μ := by
    intro N
    have hG := garsia_maximal_inequality (T := T) (f := E.indicator g) hT hgE N.succ_pos
    
    have hset : {x | 0 < maxPartialSum T (E.indicator g) (N + 1) N.succ_pos x} = s N := rfl
    rw [hset] at hG
    
    rwa [setIntegral_congr_fun₀ (hs_meas N)
      (fun x hx => Set.indicator_of_mem (hs_subE N hx) g)] at hG
  
  have hlim : Tendsto (fun N => ∫ x in s N, g x ∂μ) atTop (𝓝 (∫ x in E, g x ∂μ)) := by
    have h := tendsto_setIntegral_of_monotone₀ (μ := μ) (f := g) hs_meas hs_mono
      (by rw [hs_union]; exact hg.integrableOn)
    rwa [hs_union] at h
  exact ge_of_tendsto' hlim hgarsia


theorem aestronglyMeasurable_birkhoffAverage (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    (n : ℕ) : AEStronglyMeasurable (fun x => birkhoffAverage ℝ T f n x) μ := by
  have hbs : Integrable (fun x => birkhoffSum T f n x) μ := by
    simp only [birkhoffSum]
    refine integrable_finsetSum _ fun i _ => ?_
    rw [← memLp_one_iff_integrable] at hf ⊢
    exact hf.comp_measurePreserving (hT.iterate i)
  simp only [birkhoffAverage]
  exact AEStronglyMeasurable.const_smul hbs.aestronglyMeasurable ((n : ℝ)⁻¹)


theorem aemeasurable_coe_birkhoffAverage (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    (n : ℕ) : AEMeasurable (fun x => ((birkhoffAverage ℝ T f n x : ℝ) : EReal)) μ :=
  measurable_coe_real_ereal.comp_aemeasurable
    (aestronglyMeasurable_birkhoffAverage hT hf n).aemeasurable


theorem aemeasurable_fStar (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    AEMeasurable (fStar T f) μ := by
  have hA := aemeasurable_coe_birkhoffAverage hT hf
  refine ⟨fun x => limsup (fun n => (hA n).mk _ x) atTop,
    Measurable.limsup (fun n => (hA n).measurable_mk), ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n, ((birkhoffAverage ℝ T f n x : ℝ) : EReal) = (hA n).mk _ x := by
    rw [ae_all_iff]; exact fun n => (hA n).ae_eq_mk
  filter_upwards [hall] with x hx
  exact limsup_congr (Eventually.of_forall fun n => hx n)


theorem aemeasurable_fStarLow (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    AEMeasurable (fStarLow T f) μ := by
  have hA := aemeasurable_coe_birkhoffAverage hT hf
  refine ⟨fun x => liminf (fun n => (hA n).mk _ x) atTop,
    Measurable.liminf (fun n => (hA n).measurable_mk), ?_⟩
  have hall : ∀ᵐ x ∂μ, ∀ n, ((birkhoffAverage ℝ T f n x : ℝ) : EReal) = (hA n).mk _ x := by
    rw [ae_all_iff]; exact fun n => (hA n).ae_eq_mk
  filter_upwards [hall] with x hx
  exact liminf_congr (Eventually.of_forall fun n => hx n)


omit [MeasurableSpace α] in

theorem birkhoffSum_sub_const (b : ℝ) (n : ℕ) (x : α) :
    birkhoffSum T (fun y => f y - b) n x = birkhoffSum T f n x - n • b := by
  have hsub := birkhoffSum_sub_apply T f (fun _ => b) n x
  have hconst : (fun (_ : α) => b) ∘ T = (fun (_ : α) => b) := rfl
  rw [show (fun y => f y - b) = f - (fun _ => b) from rfl, hsub, birkhoffSum_apply_of_comp_eq hconst n x]

omit [MeasurableSpace α] in


theorem exists_birkhoffSum_sub_pos {b : ℝ} {x : α} (hx : (b : EReal) < fStar T f x) :
    ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T (fun y => f y - b) n x := by
  have hfreq : ∃ᶠ n in atTop, (b : EReal) < ((birkhoffAverage ℝ T f n x : ℝ) : EReal) :=
    frequently_lt_of_lt_limsup (by isBoundedDefault) hx
  have hfreq' : ∃ᶠ n in atTop, 1 ≤ n ∧ b < birkhoffAverage ℝ T f n x := by
    refine hfreq.mp ?_
    filter_upwards [eventually_ge_atTop 1] with n hn hlt
    exact ⟨hn, by exact_mod_cast hlt⟩
  obtain ⟨n, hn1, hlt⟩ := hfreq'.exists
  refine ⟨n, hn1, ?_⟩
  
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [birkhoffSum_sub_const]
  simp only [birkhoffAverage, smul_eq_mul] at hlt
  rw [nsmul_eq_mul]
  
  have hmul : (n : ℝ) * b < (n : ℝ) * ((n : ℝ)⁻¹ * birkhoffSum T f n x) :=
    mul_lt_mul_of_pos_left hlt hn0
  rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hn0), one_mul] at hmul
  linarith

omit [MeasurableSpace α] in


theorem exists_birkhoffSum_sub_pos' {a : ℝ} {x : α} (hx : fStarLow T f x < (a : EReal)) :
    ∃ n, 1 ≤ n ∧ 0 < birkhoffSum T (fun y => a - f y) n x := by
  
  have hx' : ((-a : ℝ) : EReal) < fStar T (-f) (x) := by
    rw [fStarLow_eq_neg_fStar_neg] at hx
    have h1 : -fStar T (-f) x < (a : EReal) := hx
    rw [EReal.coe_neg]
    exact EReal.neg_lt_comm.mp h1
  obtain ⟨n, hn1, hpos⟩ := exists_birkhoffSum_sub_pos (f := -f) (b := -a) (x := x) hx'
  refine ⟨n, hn1, ?_⟩
  have hcongr : (fun y => (-f) y - (-a)) = (fun y => a - f y) := by funext y; simp; ring
  rwa [hcongr] at hpos


end BirkhoffAE
end StatMech
