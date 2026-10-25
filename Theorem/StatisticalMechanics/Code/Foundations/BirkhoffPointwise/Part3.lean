/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/BirkhoffPointwise.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.MaximalErgodicGarsia
import Def.StatisticalMechanics.Code.Foundations.BirkhoffPointwise.Part3
open MeasureTheory Filter Finset Function MeasurableSpace
open scoped Topology ENNReal


namespace StatMech

namespace BirkhoffAE

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {T : α → α} {f : α → ℝ}


variable [IsFiniteMeasure μ]


omit [MeasurableSpace α] [IsFiniteMeasure μ] in

theorem isInvariantSet_levelSet (a b : ℝ) : IsInvariantSet T (levelSet T f a b) := by
  intro x
  simp only [levelSet, Set.mem_setOf_eq, fStar_comp, fStarLow_comp]

omit [IsFiniteMeasure μ] in

theorem nullMeasurableSet_levelSet (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) (a b : ℝ) :
    NullMeasurableSet (levelSet T f a b) μ := by
  have h1 : NullMeasurableSet {x | fStarLow T f x < (a : EReal)} μ :=
    nullMeasurableSet_lt (aemeasurable_fStarLow hT hf) aemeasurable_const
  have h2 : NullMeasurableSet {x | (b : EReal) < fStar T f x} μ :=
    nullMeasurableSet_lt aemeasurable_const (aemeasurable_fStar hT hf)
  exact h1.inter h2


theorem setIntegral_ge_of_lt_fStar (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {b : ℝ} {E : Set α} (hEmeas : NullMeasurableSet E μ) (hEinv : IsInvariantSet T E)
    (hE : ∀ x ∈ E, (b : EReal) < fStar T f x) :
    b * (μ E).toReal ≤ ∫ x in E, f x ∂μ := by
  have hgb : Integrable (fun y => f y - b) μ := hf.sub (integrable_const b)
  have hnn : 0 ≤ ∫ x in E, (f x - b) ∂μ :=
    setIntegral_nonneg_of_invariant hT hgb hEmeas hEinv
      (fun x hx => exists_birkhoffSum_sub_pos (hE x hx))
  have hsplit : ∫ x in E, (f x - b) ∂μ = (∫ x in E, f x ∂μ) - b * (μ E).toReal := by
    rw [integral_sub hf.integrableOn (integrable_const b).integrableOn, setIntegral_const,
      smul_eq_mul, mul_comm, Measure.real]
  linarith [hsplit ▸ hnn]


theorem setIntegral_le_of_fStarLow_lt (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {a : ℝ} {E : Set α} (hEmeas : NullMeasurableSet E μ) (hEinv : IsInvariantSet T E)
    (hE : ∀ x ∈ E, fStarLow T f x < (a : EReal)) :
    ∫ x in E, f x ∂μ ≤ a * (μ E).toReal := by
  have hga : Integrable (fun y => a - f y) μ := (integrable_const a).sub hf
  have hnn : 0 ≤ ∫ x in E, (a - f x) ∂μ :=
    setIntegral_nonneg_of_invariant hT hga hEmeas hEinv
      (fun x hx => exists_birkhoffSum_sub_pos' (hE x hx))
  have hsplit : ∫ x in E, (a - f x) ∂μ = a * (μ E).toReal - ∫ x in E, f x ∂μ := by
    rw [integral_sub (integrable_const a).integrableOn hf.integrableOn, setIntegral_const,
      smul_eq_mul, mul_comm, Measure.real]
  linarith [hsplit ▸ hnn]


theorem measure_levelSet_eq_zero (hT : MeasurePreserving T μ μ) (hf : Integrable f μ)
    {a b : ℝ} (hab : a < b) : μ (levelSet T f a b) = 0 := by
  set E := levelSet T f a b with hEdef
  have hEinv : IsInvariantSet T E := isInvariantSet_levelSet a b
  have hEmeas : NullMeasurableSet E μ := nullMeasurableSet_levelSet hT hf a b
  set m : ℝ := (μ E).toReal with hm
  have hlow : b * m ≤ ∫ x in E, f x ∂μ :=
    setIntegral_ge_of_lt_fStar hT hf hEmeas hEinv (fun x hx => hx.2)
  have hupp : ∫ x in E, f x ∂μ ≤ a * m :=
    setIntegral_le_of_fStarLow_lt hT hf hEmeas hEinv (fun x hx => hx.1)
  
  have hbm_le_am : b * m ≤ a * m := le_trans hlow hupp
  have hm_nonneg : 0 ≤ m := ENNReal.toReal_nonneg
  have hm_zero : m = 0 := by
    by_contra hne
    have hm_pos : 0 < m := lt_of_le_of_ne hm_nonneg (Ne.symm hne)
    nlinarith [hbm_le_am, hab, hm_pos]
  have hfin : μ E ≠ ∞ := measure_ne_top μ E
  rwa [hm, ENNReal.toReal_eq_zero_iff, or_iff_left hfin] at hm_zero


theorem fStar_lt_top_ae (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, fStar T f x < ⊤ := by
  set C : ℝ := ∫ x, |f x| ∂μ with hC
  have hCnn : 0 ≤ C := integral_nonneg (fun x => abs_nonneg _)
  
  have htop : μ {x | fStar T f x = ⊤} = 0 := by
    set S : Set α := {x | fStar T f x = ⊤} with hSdef
    have hSmeas : NullMeasurableSet S μ := by
      have : S = (fStar T f) ⁻¹' {⊤} := by ext x; simp [hSdef]
      rw [this]
      exact (aemeasurable_fStar hT hf).nullMeasurableSet_preimage (measurableSet_singleton ⊤)
    
    have hbound : ∀ n : ℕ, 1 ≤ n → (n : ℝ) * (μ S).toReal ≤ C := by
      intro n hn
      set E : Set α := {x | ((n : ℝ) : EReal) < fStar T f x} with hEdef
      have hEinv : IsInvariantSet T E := by
        intro x; simp only [hEdef, Set.mem_setOf_eq, fStar_comp]
      have hEmeas : NullMeasurableSet E μ :=
        nullMeasurableSet_lt aemeasurable_const (aemeasurable_fStar hT hf)
      have hSsubE : S ⊆ E := by
        intro x hx
        simp only [hEdef, Set.mem_setOf_eq]
        rw [show fStar T f x = ⊤ from hx]; exact EReal.coe_lt_top _
      have hge : (n : ℝ) * (μ E).toReal ≤ ∫ x in E, f x ∂μ :=
        setIntegral_ge_of_lt_fStar hT hf hEmeas hEinv (fun x hx => hx)
      have hfle : ∫ x in E, f x ∂μ ≤ C := by
        calc ∫ x in E, f x ∂μ ≤ ∫ x in E, |f x| ∂μ :=
              setIntegral_mono_ae hf.integrableOn (hf.abs).integrableOn
                (Eventually.of_forall fun x => le_abs_self _)
          _ ≤ C := by
              rw [hC]
              exact setIntegral_le_integral hf.abs (Eventually.of_forall fun x => abs_nonneg _)
      have hSEle : (μ S).toReal ≤ (μ E).toReal :=
        measureReal_mono hSsubE
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      calc (n : ℝ) * (μ S).toReal ≤ (n : ℝ) * (μ E).toReal := by gcongr
        _ ≤ ∫ x in E, f x ∂μ := hge
        _ ≤ C := hfle
    
    have hmSnn : 0 ≤ (μ S).toReal := ENNReal.toReal_nonneg
    have hmS0 : (μ S).toReal = 0 := by
      by_contra hne
      have hpos : 0 < (μ S).toReal := lt_of_le_of_ne hmSnn (Ne.symm hne)
      
      obtain ⟨n, hn⟩ := exists_nat_gt (C / (μ S).toReal)
      have hn1 : 1 ≤ max n 1 := le_max_right _ _
      have hbd := hbound (max n 1) hn1
      have hnle : (n : ℝ) ≤ (max n 1 : ℕ) := by exact_mod_cast le_max_left _ _
      have : C / (μ S).toReal < (max n 1 : ℕ) := lt_of_lt_of_le hn hnle
      rw [div_lt_iff₀ hpos] at this
      nlinarith [hbd, this]
    have hfin : μ S ≠ ∞ := measure_ne_top μ S
    rwa [ENNReal.toReal_eq_zero_iff, or_iff_left hfin] at hmS0
  
  rw [ae_iff]
  refine measure_mono_null (fun x hx => ?_) htop
  simp only [not_lt, top_le_iff] at hx
  exact hx


theorem fStarLow_bot_lt_ae (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, ⊥ < fStarLow T f x := by
  have h := fStar_lt_top_ae hT (f := -f) hf.neg
  filter_upwards [h] with x hx
  rw [fStarLow_eq_neg_fStar_neg]
  rw [show (⊥ : EReal) = -(⊤ : EReal) from rfl]
  exact EReal.neg_lt_neg_iff.mpr hx


theorem fStarLow_ae_eq_fStar (hT : MeasurePreserving T μ μ) (hf : Integrable f μ) :
    fStarLow T f =ᵐ[μ] fStar T f := by
  
  have hnull : μ {x | fStarLow T f x < fStar T f x} = 0 := by
    refine measure_mono_null
      (t := ⋃ q : {q : ℚ × ℚ // q.1 < q.2}, levelSet T f (q.1.1 : ℝ) (q.1.2 : ℝ)) ?_ ?_
    · intro x hx
      simp only [Set.mem_setOf_eq] at hx
      obtain ⟨b, hub, hbv⟩ := EReal.lt_iff_exists_rat_btwn.mp hx
      obtain ⟨a, hua, hab⟩ := EReal.lt_iff_exists_rat_btwn.mp hub
      have hab' : a < b := by exact_mod_cast (EReal.coe_lt_coe_iff.mp hab)
      exact Set.mem_iUnion.mpr ⟨⟨(a, b), hab'⟩, hua, hbv⟩
    · refine measure_iUnion_null fun q => measure_levelSet_eq_zero hT hf ?_
      exact_mod_cast q.2
  rw [Filter.EventuallyEq, ae_iff]
  
  have hle : ∀ x, fStarLow T f x ≤ fStar T f x := fun x => by
    unfold fStarLow fStar; exact liminf_le_limsup
  refine measure_mono_null (fun x hx => ?_) hnull
  simp only [Set.mem_setOf_eq] at hx ⊢
  exact lt_of_le_of_ne (hle x) hx


end BirkhoffAE
end StatMech
