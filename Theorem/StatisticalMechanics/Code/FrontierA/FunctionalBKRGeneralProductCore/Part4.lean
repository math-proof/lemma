/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRFiniteCoordinateBlocks.Part6
import Mathlib.MeasureTheory.Function.EssSup
import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part4
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


theorem measurable_piCylinderSublevelMeasure
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf : Measurable f)
    (K : Set E) (r : ℝ) :
    Measurable (piCylinderSublevelMeasure μ f K r) := by
  let A : Set ((∀ e, S e) × PiFiberFreeConfig (S := S) K) :=
    {p | f (piFiberAssemble K p.1 p.2) ≤ r}
  have hA : MeasurableSet A := by
    exact measurableSet_le
      (hf.comp (measurable_piFiberAssemble_uncurry K)) measurable_const
  have hm := measurable_measure_prodMk_left
    (ν := Measure.pi fun i : {e : E // e ∉ K} => μ i) hA
  simpa only [piCylinderSublevelMeasure, A] using hm

theorem lt_piCylinderEssInf_iff
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf0 : ∀ x, 0 ≤ f x)
    (K : Set E) (x : ∀ e, S e) (a : ℝ) :
    a < piCylinderEssInf μ f K x ↔
      ∃ n : ℕ, piCylinderSublevelMeasure μ f K
        (a + 1 / (n + 1 : ℝ)) x = 0 := by
  let h : PiFiberFreeConfig (S := S) K → ℝ :=
    fun z => f (piFiberAssemble K x z)
  let ν : Measure (PiFiberFreeConfig (S := S) K) :=
    Measure.pi fun i : {e : E // e ∉ K} => μ i
  letI : IsProbabilityMeasure ν := by
    dsimp only [ν]
    infer_instance
  have hh0 : ∀ z, 0 ≤ h z := fun z => hf0 _
  have hbounded : Filter.IsBoundedUnder (fun p q : ℝ => p ≥ q)
      (ae ν) h := by
    change ∃ b : ℝ, ∀ᵐ z ∂ν, h z ≥ b
    exact ⟨0, Filter.Eventually.of_forall hh0⟩
  constructor
  · intro ha
    have ha' : a < essInf h ν := by
      simpa only [piCylinderEssInf, h, ν] using ha
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr ha')
    have hr : a + 1 / (n + 1 : ℝ) < essInf h ν := by
      linarith
    have hae : ∀ᵐ z ∂ν, a + 1 / (n + 1 : ℝ) < h z :=
      ae_lt_of_lt_essInf hr hbounded
    refine ⟨n, ?_⟩
    rw [piCylinderSublevelMeasure, measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with z hz
    exact not_le_of_gt hz
  · rintro ⟨n, hn⟩
    have hae : ∀ᵐ z ∂ν,
        a + 1 / (n + 1 : ℝ) ≤ h z := by
      rw [piCylinderSublevelMeasure,
        measure_eq_zero_iff_ae_notMem] at hn
      filter_upwards [hn] with z hz
      exact le_of_lt (lt_of_not_ge hz)
    have hrle : a + 1 / (n + 1 : ℝ) ≤ essInf h ν :=
      le_essInf_of_ae_le _ hae
        (ae_isCoboundedUnder_ge_real ν h)
    have hpos : 0 < 1 / (n + 1 : ℝ) := by positivity
    exact lt_of_lt_of_le (lt_add_of_pos_right a hpos) hrle


theorem measurable_piCylinderEssInf
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (K : Set E) :
    Measurable (piCylinderEssInf μ f K) := by
  apply measurable_of_Ioi
  intro a
  have hpre : piCylinderEssInf μ f K ⁻¹' Ioi a =
      ⋃ n : ℕ, {x | piCylinderSublevelMeasure μ f K
        (a + 1 / (n + 1 : ℝ)) x = 0} := by
    ext x
    simp only [mem_preimage, mem_Ioi, mem_iUnion, mem_setOf_eq]
    exact lt_piCylinderEssInf_iff μ f hf0 K x a
  rw [hpre]
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_singleton 0 |>.preimage
    (measurable_piCylinderSublevelMeasure μ f hf K _)


theorem piCylinderEssInf_le_ae
    (μ : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (μ e)]
    (f : (∀ e, S e) → ℝ) (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (K : Set E) :
    ∀ᵐ x ∂Measure.pi μ, piCylinderEssInf μ f K x ≤ f x := by
  classical
  let split := piFiberSplit (S := S) K
  let μK : Measure (∀ i : {e : E // e ∈ K}, S i) :=
    Measure.pi fun i : {e : E // e ∈ K} => μ i
  let μC : Measure (PiFiberFreeConfig (S := S) K) :=
    Measure.pi fun i : {e : E // e ∉ K} => μ i
  let P : ((∀ i : {e : E // e ∈ K}, S i) ×
      PiFiberFreeConfig (S := S) K) → Prop := fun p =>
    piCylinderEssInf μ f K (split.symm p) ≤ f (split.symm p)
  have hP : MeasurableSet {p | P p} := by
    exact measurableSet_le
      ((measurable_piCylinderEssInf μ f hf hf0 K).comp split.symm.measurable)
      (hf.comp split.symm.measurable)
  have hprod : ∀ᵐ p ∂μK.prod μC, P p := by
    rw [Measure.ae_prod_iff_ae_ae hP]
    refine Filter.Eventually.of_forall fun u => ?_
    let h : PiFiberFreeConfig (S := S) K → ℝ :=
      fun w => f (split.symm (u, w))
    have hbounded : Filter.IsBoundedUnder (fun a b : ℝ => a ≥ b)
        (ae μC) h := by
      change ∃ b : ℝ, ∀ᵐ w ∂μC, h w ≥ b
      exact ⟨0, Filter.Eventually.of_forall fun w => hf0 _⟩
    have hae : ∀ᵐ v ∂μC, essInf h μC ≤ h v :=
      ae_essInf_le hbounded
    filter_upwards [hae] with v hv
    simpa only [P, piCylinderEssInf, h, μC, split,
      piFiberAssemble_piEquiv_symm] using hv
  have hmp : MeasurePreserving split (Measure.pi μ) (μK.prod μC) := by
    simpa only [split, piFiberSplit, μK, μC] using
      (measurePreserving_piEquivPiSubtypeProd μ (fun e => e ∈ K))
  rw [← hmp.map_eq] at hprod
  have hpull := (ae_map_iff hmp.measurable.aemeasurable hP).mp hprod
  filter_upwards [hpull] with x hx
  have hs : split.symm (split x) = x := split.symm_apply_apply x
  simpa only [P, hs] using hx


end StatMech.FrontierA
