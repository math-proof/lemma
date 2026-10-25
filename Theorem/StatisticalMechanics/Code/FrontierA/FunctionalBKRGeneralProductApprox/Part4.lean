/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
import Def.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductApprox.Part3
open MeasureTheory Set
open Filter Topology
open scoped BigOperators ENNReal symmDiff


namespace StatMech.FrontierA

universe u v

variable {E : Type u} [Fintype E] [DecidableEq E]
  {S : E → Type v} [∀ e, MeasurableSpace (S e)]


theorem exists_finiteCoordinateSet_dependsOn_symmDiff_lt
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (K : Set E) {A : Set (∀ e, S e)} (hA : MeasurableSet A)
    (hdep : PiSetDependsOn K A) {eps : ℝ≥0∞} (heps : 0 < eps) :
    ∃ B, IsFiniteCoordinateSet B ∧ PiSetDependsOn K B ∧
      Measure.pi mu (B ∆ A) < eps := by
  classical
  letI : ∀ e, Nonempty (S e) := fun e => nonempty_of_isProbabilityMeasure (mu e)
  let base : ∀ e, S e := fun e => Classical.choice inferInstance
  let AK : Set (∀ i : {e : E // e ∈ K}, S i) :=
    piExtendOn K base ⁻¹' A
  have hAK : MeasurableSet AK := hA.preimage (measurable_piExtendOn K base)
  let muK : ∀ i : {e : E // e ∈ K}, Measure (S i) := fun i => mu i
  obtain ⟨BK, hBKfin, hBKerr⟩ :=
    exists_finiteCoordinateSet_symmDiff_lt muK hAK heps
  let B : Set (∀ e, S e) := piRestrict K ⁻¹' BK
  refine ⟨B, hBKfin.preimage_piRestrict K, ?_, ?_⟩
  · intro x y hxy
    have hr : piRestrict K x = piRestrict K y := by
      funext i
      exact hxy i i.property
    simp [B, hr]
  · have hAeq : A = piRestrict K ⁻¹' AK := by
      ext x
      simp only [AK, Set.mem_preimage]
      exact hdep (piExtendOn_agreeOn K base x)
    rw [hAeq, ← Set.preimage_symmDiff]
    exact (measurePreserving_piRestrict mu K).measure_preimage
      (hBKfin.measurableSet.symmDiff hAK).nullMeasurableSet |>.trans_lt hBKerr


theorem measurable_piFunctionalFamilyMax
    (F : Set E → (∀ e, S e) → ℝ) (hF : ∀ K, Measurable (F K)) :
    Measurable (piFunctionalFamilyMax F) := by
  have hrw : piFunctionalFamilyMax F =
      (Finset.univ : Finset (Set E)).sup'
        (Finset.univ_nonempty : (Finset.univ : Finset (Set E)).Nonempty) F := by
    funext x
    rw [piFunctionalFamilyMax, Finset.sup'_apply]
  rw [hrw]
  exact Finset.measurable_sup' _ fun K _ => hF K

theorem measurable_piFunctionalFamilyDisjointMax
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF : ∀ K, Measurable (F K)) (hG : ∀ K, Measurable (G K)) :
    Measurable (piFunctionalFamilyDisjointMax F G) := by
  have hrw : piFunctionalFamilyDisjointMax F G =
      (disjointCoordinatePairs E).sup'
        (disjointCoordinatePairs_nonempty (E := E))
        (fun pair x => F pair.1 x * G pair.2 x) := by
    funext x
    rw [piFunctionalFamilyDisjointMax, piFunctionalFamilyDisjointMaxAt,
      Finset.sup'_apply]
  rw [hrw]
  exact Finset.measurable_sup' _ fun pair _ => (hF pair.1).mul (hG pair.2)

theorem measurable_piFunctionalFamilyDisjointMaxAt
    (F G : Set E → (∀ e, S e) → ℝ)
    (hF : ∀ K, Measurable (F K)) (hG : ∀ K, Measurable (G K)) :
    Measurable (fun p : (∀ e, S e) × (∀ e, S e) =>
      piFunctionalFamilyDisjointMaxAt F G p.1 p.2) := by
  have hrw : (fun p : (∀ e, S e) × (∀ e, S e) =>
      piFunctionalFamilyDisjointMaxAt F G p.1 p.2) =
      (disjointCoordinatePairs E).sup'
        (disjointCoordinatePairs_nonempty (E := E))
        (fun pair p => F pair.1 p.1 * G pair.2 p.2) := by
    funext p
    rw [piFunctionalFamilyDisjointMaxAt, Finset.sup'_apply]
  rw [hrw]
  exact Finset.measurable_sup' _ fun pair _ =>
    ((hF pair.1).comp measurable_fst).mul ((hG pair.2).comp measurable_snd)

theorem piFunctionalFamilyMax_le
    (F : Set E → (∀ e, S e) → ℝ) {C : ℝ}
    (hF : ∀ K x, F K x ≤ C) (x : ∀ e, S e) :
    piFunctionalFamilyMax F x ≤ C := by
  unfold piFunctionalFamilyMax
  apply Finset.sup'_le
  intro K _
  exact hF K x

theorem piFunctionalFamilyDisjointMax_le
    (F G : Set E → (∀ e, S e) → ℝ) {C D : ℝ}
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K x, F K x ≤ C) (hG : ∀ K x, G K x ≤ D)
    (x : ∀ e, S e) :
    piFunctionalFamilyDisjointMax F G x ≤ C * D := by
  unfold piFunctionalFamilyDisjointMax piFunctionalFamilyDisjointMaxAt
  apply Finset.sup'_le
  intro pair _
  exact mul_le_mul (hF pair.1 x) (hG pair.2 x) (hG0 pair.2 x)
    (le_trans (hF0 pair.1 x) (hF pair.1 x))

theorem piFunctionalFamilyDisjointMaxAt_le_bound
    (F G : Set E → (∀ e, S e) → ℝ) {C D : ℝ}
    (hF0 : ∀ K x, 0 ≤ F K x) (hG0 : ∀ K x, 0 ≤ G K x)
    (hF : ∀ K x, F K x ≤ C) (hG : ∀ K x, G K x ≤ D)
    (x y : ∀ e, S e) :
    piFunctionalFamilyDisjointMaxAt F G x y ≤ C * D := by
  unfold piFunctionalFamilyDisjointMaxAt
  apply Finset.sup'_le
  intro pair _
  exact mul_le_mul (hF pair.1 x) (hG pair.2 y) (hG0 pair.2 y)
    (le_trans (hF0 pair.1 x) (hF pair.1 x))

theorem tendsto_piFunctionalFamilyMax
    (F : ℕ → Set E → (∀ e, S e) → ℝ)
    (Flim : Set E → (∀ e, S e) → ℝ) (x : ∀ e, S e)
    (h : ∀ K, Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x))) :
    Tendsto (fun n => piFunctionalFamilyMax (F n) x) atTop
      (𝓝 (piFunctionalFamilyMax Flim x)) := by
  unfold piFunctionalFamilyMax
  exact Tendsto.finset_sup'_nhds_apply Finset.univ_nonempty
    (fun K _ => h K)

theorem tendsto_piFunctionalFamilyDisjointMax
    (F G : ℕ → Set E → (∀ e, S e) → ℝ)
    (Flim Glim : Set E → (∀ e, S e) → ℝ) (x : ∀ e, S e)
    (hF : ∀ K, Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x)))
    (hG : ∀ K, Tendsto (fun n => G n K x) atTop (𝓝 (Glim K x))) :
    Tendsto (fun n => piFunctionalFamilyDisjointMax (F n) (G n) x) atTop
      (𝓝 (piFunctionalFamilyDisjointMax Flim Glim x)) := by
  unfold piFunctionalFamilyDisjointMax piFunctionalFamilyDisjointMaxAt
  exact Tendsto.finset_sup'_nhds_apply (disjointCoordinatePairs_nonempty (E := E))
    (fun pair _ => (hF pair.1).mul (hG pair.2))

theorem tendsto_piFunctionalFamilyDisjointMaxAt
    (F G : ℕ → Set E → (∀ e, S e) → ℝ)
    (Flim Glim : Set E → (∀ e, S e) → ℝ) (x y : ∀ e, S e)
    (hF : ∀ K, Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x)))
    (hG : ∀ K, Tendsto (fun n => G n K y) atTop (𝓝 (Glim K y))) :
    Tendsto (fun n => piFunctionalFamilyDisjointMaxAt (F n) (G n) x y) atTop
      (𝓝 (piFunctionalFamilyDisjointMaxAt Flim Glim x y)) := by
  unfold piFunctionalFamilyDisjointMaxAt
  exact Tendsto.finset_sup'_nhds_apply (disjointCoordinatePairs_nonempty (E := E))
    (fun pair _ => (hF pair.1).mul (hG pair.2))

theorem measurableFamilyBKR_of_bounded_ae_limit
    (mu : ∀ e, Measure (S e)) [∀ e, IsProbabilityMeasure (mu e)]
    (F G : ℕ → Set E → (∀ e, S e) → ℝ)
    (Flim Glim : Set E → (∀ e, S e) → ℝ)
    (C D : ℝ) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hFm : ∀ n K, Measurable (F n K))
    (hGm : ∀ n K, Measurable (G n K))
    (hFlimm : ∀ K, Measurable (Flim K))
    (hGlimm : ∀ K, Measurable (Glim K))
    (hF0 : ∀ n K x, 0 ≤ F n K x)
    (hG0 : ∀ n K x, 0 ≤ G n K x)
    (hFlim0 : ∀ K x, 0 ≤ Flim K x)
    (hGlim0 : ∀ K x, 0 ≤ Glim K x)
    (hFC : ∀ n K x, F n K x ≤ C)
    (hGD : ∀ n K x, G n K x ≤ D)
    (hFlimC : ∀ K x, Flim K x ≤ C)
    (hGlimD : ∀ K x, Glim K x ≤ D)
    (hconvF : ∀ K, ∀ᵐ x ∂Measure.pi mu,
      Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x)))
    (hconvG : ∀ K, ∀ᵐ x ∂Measure.pi mu,
      Tendsto (fun n => G n K x) atTop (𝓝 (Glim K x)))
    (hineq : ∀ n,
      (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax (F n) (G n) x)
          ∂Measure.pi mu) ≤
          (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (F n) x)
            ∂Measure.pi mu) *
          ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (G n) x)
            ∂Measure.pi mu ∧
        (∫⁻ p, ENNReal.ofReal
            (piFunctionalFamilyDisjointMaxAt (F n) (G n) p.1 p.2)
            ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
          ∫⁻ x, ENNReal.ofReal
            (piFunctionalFamilyMax (F n) x * piFunctionalFamilyMax (G n) x)
            ∂Measure.pi mu) :
    (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax Flim Glim x)
        ∂Measure.pi mu) ≤
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Flim x)
          ∂Measure.pi mu) *
        ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Glim x)
          ∂Measure.pi mu ∧
      (∫⁻ p, ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt Flim Glim p.1 p.2)
          ∂(Measure.pi mu).prod (Measure.pi mu)) ≤
        ∫⁻ x, ENNReal.ofReal
          (piFunctionalFamilyMax Flim x * piFunctionalFamilyMax Glim x)
          ∂Measure.pi mu := by
  have hconvFall : ∀ᵐ x ∂Measure.pi mu, ∀ K,
      Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x)) :=
    ae_all_iff.mpr hconvF
  have hconvGall : ∀ᵐ x ∂Measure.pi mu, ∀ K,
      Tendsto (fun n => G n K x) atTop (𝓝 (Glim K x)) :=
    ae_all_iff.mpr hconvG
  have hlimMaxF : ∀ᵐ x ∂Measure.pi mu,
      Tendsto (fun n => ENNReal.ofReal (piFunctionalFamilyMax (F n) x)) atTop
        (𝓝 (ENNReal.ofReal (piFunctionalFamilyMax Flim x))) := by
    filter_upwards [hconvFall] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_piFunctionalFamilyMax F Flim x hx)
  have hlimMaxG : ∀ᵐ x ∂Measure.pi mu,
      Tendsto (fun n => ENNReal.ofReal (piFunctionalFamilyMax (G n) x)) atTop
        (𝓝 (ENNReal.ofReal (piFunctionalFamilyMax Glim x))) := by
    filter_upwards [hconvGall] with x hx
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_piFunctionalFamilyMax G Glim x hx)
  have hlimDisjoint : ∀ᵐ x ∂Measure.pi mu,
      Tendsto (fun n => ENNReal.ofReal
        (piFunctionalFamilyDisjointMax (F n) (G n) x)) atTop
        (𝓝 (ENNReal.ofReal (piFunctionalFamilyDisjointMax Flim Glim x))) := by
    filter_upwards [hconvFall, hconvGall] with x hxF hxG
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_piFunctionalFamilyDisjointMax F G Flim Glim x hxF hxG)
  have hlimSameProduct : ∀ᵐ x ∂Measure.pi mu,
      Tendsto (fun n => ENNReal.ofReal
        (piFunctionalFamilyMax (F n) x * piFunctionalFamilyMax (G n) x)) atTop
        (𝓝 (ENNReal.ofReal
          (piFunctionalFamilyMax Flim x * piFunctionalFamilyMax Glim x))) := by
    filter_upwards [hconvFall, hconvGall] with x hxF hxG
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((tendsto_piFunctionalFamilyMax F Flim x hxF).mul
        (tendsto_piFunctionalFamilyMax G Glim x hxG))
  have hconvFfst : ∀ᵐ p ∂(Measure.pi mu).prod (Measure.pi mu), ∀ K,
      Tendsto (fun n => F n K p.1) atTop (𝓝 (Flim K p.1)) :=
    Measure.quasiMeasurePreserving_fst.ae hconvFall
  have hconvGsnd : ∀ᵐ p ∂(Measure.pi mu).prod (Measure.pi mu), ∀ K,
      Tendsto (fun n => G n K p.2) atTop (𝓝 (Glim K p.2)) :=
    Measure.quasiMeasurePreserving_snd.ae hconvGall
  have hlimDual : ∀ᵐ p ∂(Measure.pi mu).prod (Measure.pi mu),
      Tendsto (fun n => ENNReal.ofReal
        (piFunctionalFamilyDisjointMaxAt (F n) (G n) p.1 p.2)) atTop
        (𝓝 (ENNReal.ofReal
          (piFunctionalFamilyDisjointMaxAt Flim Glim p.1 p.2))) := by
    filter_upwards [hconvFfst, hconvGsnd] with p hpF hpG
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      (tendsto_piFunctionalFamilyDisjointMaxAt F G Flim Glim p.1 p.2 hpF hpG)
  have hfinC : (∫⁻ _ : (∀ e, S e), ENNReal.ofReal C ∂Measure.pi mu) ≠ ∞ := by
    simp [ENNReal.ofReal_ne_top]
  have hfinD : (∫⁻ _ : (∀ e, S e), ENNReal.ofReal D ∂Measure.pi mu) ≠ ∞ := by
    simp [ENNReal.ofReal_ne_top]
  have hfinCD : (∫⁻ _ : (∀ e, S e), ENNReal.ofReal (C * D)
      ∂Measure.pi mu) ≠ ∞ := by
    simp [ENNReal.ofReal_ne_top]
  have hfinCDprod : (∫⁻ _ : (∀ e, S e) × (∀ e, S e),
      ENNReal.ofReal (C * D) ∂(Measure.pi mu).prod (Measure.pi mu)) ≠ ∞ := by
    simp [ENNReal.ofReal_ne_top]
  have tMaxF := tendsto_lintegral_of_dominated_convergence
    (fun _ : (∀ e, S e) => ENNReal.ofReal C)
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_piFunctionalFamilyMax (F n) (hFm n)))
    (fun n => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal
      (piFunctionalFamilyMax_le (F n) (hFC n) x)) hfinC hlimMaxF
  have tMaxG := tendsto_lintegral_of_dominated_convergence
    (fun _ : (∀ e, S e) => ENNReal.ofReal D)
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_piFunctionalFamilyMax (G n) (hGm n)))
    (fun n => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal
      (piFunctionalFamilyMax_le (G n) (hGD n) x)) hfinD hlimMaxG
  have tDisjoint := tendsto_lintegral_of_dominated_convergence
    (fun _ : (∀ e, S e) => ENNReal.ofReal (C * D))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_piFunctionalFamilyDisjointMax (F n) (G n) (hFm n) (hGm n)))
    (fun n => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal
      (piFunctionalFamilyDisjointMax_le (F n) (G n)
        (hF0 n) (hG0 n) (hFC n) (hGD n) x)) hfinCD hlimDisjoint
  have tSameProduct := tendsto_lintegral_of_dominated_convergence
    (fun _ : (∀ e, S e) => ENNReal.ofReal (C * D))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      ((measurable_piFunctionalFamilyMax (F n) (hFm n)).mul
        (measurable_piFunctionalFamilyMax (G n) (hGm n))))
    (fun n => ae_of_all _ fun x => ENNReal.ofReal_le_ofReal
      (mul_le_mul (piFunctionalFamilyMax_le (F n) (hFC n) x)
        (piFunctionalFamilyMax_le (G n) (hGD n) x)
        (piFunctionalFamilyMax_nonneg (G n) (hG0 n) x)
        hC0))
    hfinCD hlimSameProduct
  have tDual := tendsto_lintegral_of_dominated_convergence
    (fun _ : (∀ e, S e) × (∀ e, S e) => ENNReal.ofReal (C * D))
    (fun n => ENNReal.continuous_ofReal.measurable.comp
      (measurable_piFunctionalFamilyDisjointMaxAt (F n) (G n)
        (hFm n) (hGm n)))
    (fun n => ae_of_all _ fun p => ENNReal.ofReal_le_ofReal
      (piFunctionalFamilyDisjointMaxAt_le_bound (F n) (G n)
        (hF0 n) (hG0 n) (hFC n) (hGD n) p.1 p.2)) hfinCDprod hlimDual
  constructor
  · have hMaxFtop : (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Flim x)
        ∂Measure.pi mu) ≠ ∞ := by
      apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top)
      calc
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Flim x) ∂Measure.pi mu) ≤
            ∫⁻ _ : (∀ e, S e), ENNReal.ofReal C ∂Measure.pi mu :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal
            (piFunctionalFamilyMax_le Flim hFlimC x)
        _ = ENNReal.ofReal C := by simp
    have hMaxGtop : (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Glim x)
        ∂Measure.pi mu) ≠ ∞ := by
      apply ne_top_of_le_ne_top (ENNReal.ofReal_ne_top)
      calc
        (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Glim x) ∂Measure.pi mu) ≤
            ∫⁻ _ : (∀ e, S e), ENNReal.ofReal D ∂Measure.pi mu :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal
            (piFunctionalFamilyMax_le Glim hGlimD x)
        _ = ENNReal.ofReal D := by simp
    exact le_of_tendsto_of_tendsto tDisjoint
      (ENNReal.Tendsto.mul tMaxF (Or.inr hMaxGtop)
        tMaxG (Or.inr hMaxFtop))
      (Eventually.of_forall fun n => (hineq n).1)
  · exact le_of_tendsto_of_tendsto tDual tSameProduct
      (Eventually.of_forall fun n => (hineq n).2)

end StatMech.FrontierA
