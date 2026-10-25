/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneSupportLexK4Literal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Realization.Part9
import Def.StatisticalMechanics.Code.Sharpness.BackboneSupportLexK4Literal.Part3
open Finset SimpleGraph
open scoped BigOperators

set_option maxHeartbeats 1600000


namespace StatMech.Sharpness

theorem shbK4CurrentEquiv_apply
    (E : Finset shbK4Edge) (m : ↑E → ℕ) (k : ↑E) :
    shbK4CurrentEquiv E m (shbK4GraphEdgeEquiv E k) = m k := by
  simp [shbK4CurrentEquiv]

theorem shbK4_oddSupport_reindex
    (E : Finset shbK4Edge) (m : ↑E → ℕ) :
    shbK4OddSupport E
        (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) =
      shbParitySupportOn E m := by
  ext k
  by_cases hk : k ∈ E
  · let ks : ↑E := ⟨k, hk⟩
    rw [shbK4Edge_mem_oddSupport]
    simp only [hk, true_and]
    have hsupport := shb_mem_paritySupportOn E m ks
    change (k ∈ shbParitySupportOn E m ↔ Odd (m ks)) at hsupport
    rw [hsupport]
    have hcode : (shbK4GraphEdgeEquiv E ks).1 = k.code := rfl
    rw [← hcode]
    unfold ofEdgeFun
    rw [dif_pos (shbK4GraphEdgeEquiv E ks).2,
      shbK4CurrentEquiv_apply]
  · simp [shbK4OddSupport, shbParitySupportOn, hk]

theorem shbK4_weight_reindex
    (E : Finset shbK4Edge) (x : ℝ) (m : ↑E → ℕ) :
    weight (shbK4Graph E) x (fun _ ↦ 1)
        (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) =
      ∏ k : ↑E, shbCurrentTerm x (m k) := by
  rw [shbK4_weight_ofEdgeFun_one]
  apply Finset.prod_congr rfl
  intro k _
  rw [shbK4CurrentEquiv_apply]
  rfl


theorem shbK4_backboneNumSupport_eq_seriesMass
    (E : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E)
    (x : ℝ) (hx : 0 ≤ x) :
    shb_backboneNumSupport (shbK4Graph E) x (fun _ ↦ 1) 0 3
        (shbK4DirectPath E h03) =
      shbK4DirectFiberSeriesMass E x := by
  unfold shb_backboneNumSupport shbK4DirectFiberSeriesMass
  rw [← (shbK4CurrentEquiv E).tsum_eq]
  calc
    (∑' m : ↑E → ℕ,
      if sources (shbK4Graph E)
            (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) = {0, 3} ∧
          shb_backboneSelectSupport (shbK4Graph E)
              (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) 0 3 =
            some (shbK4DirectPath E h03) then
        weight (shbK4Graph E) x (fun _ ↦ 1)
          (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) else 0) =
      ∑' m : ↑E → ℕ,
        if shbK4SelectsDirect03 (shbParitySupportOn E m) then
          ∏ k : ↑E, shbCurrentTerm x (m k) else 0 := by
      apply tsum_congr
      intro m
      have hfiber :
          (sources (shbK4Graph E)
                (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) = {0, 3} ∧
            shb_backboneSelectSupport (shbK4Graph E)
                (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) 0 3 =
              some (shbK4DirectPath E h03)) ↔
            shbK4SelectsDirect03 (shbParitySupportOn E m) := by
        rw [shbK4_source_selector_fiber_iff, shbK4_oddSupport_reindex]
      by_cases hsel : shbK4SelectsDirect03 (shbParitySupportOn E m)
      · rw [if_pos (hfiber.mpr hsel), if_pos hsel, shbK4_weight_reindex]
      · rw [if_neg (fun h => hsel (hfiber.mp h)), if_neg hsel]
    _ = shbParitySeriesMassOn E shbK4SelectsDirect03 x :=
      shb_current_tsum_eq_paritySeriesMassOn E shbK4SelectsDirect03 x hx


theorem shbK4_currentSum_empty_eq_seriesMass
    (E : Finset shbK4Edge) (x : ℝ) (hx : 0 ≤ x) :
    currentSum (shbK4Graph E) x (fun _ ↦ 1) ∅ =
      shbK4VacuumSeriesMass E x := by
  unfold currentSum shbK4VacuumSeriesMass
  rw [← (shbK4CurrentEquiv E).tsum_eq]
  calc
    (∑' m : ↑E → ℕ,
      if sources (shbK4Graph E)
          (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) = ∅ then
        weight (shbK4Graph E) x (fun _ ↦ 1)
          (ofEdgeFun (shbK4Graph E) (shbK4CurrentEquiv E m)) else 0) =
      ∑' m : ↑E → ℕ,
        if shbK4Boundary (shbParitySupportOn E m) = ∅ then
          ∏ k : ↑E, shbCurrentTerm x (m k) else 0 := by
      apply tsum_congr
      intro m
      rw [shbK4_sources_eq_boundary, shbK4_oddSupport_reindex,
        shbK4_weight_reindex]
    _ = shbParitySeriesMassOn E (fun A ↦ shbK4Boundary A = ∅) x :=
      shb_current_tsum_eq_paritySeriesMassOn E
        (fun A ↦ shbK4Boundary A = ∅) x hx


theorem shbK4_rhoSupport_eq_directRhoSeries
    (E : Finset shbK4Edge) (h03 : shbK4Edge.e03 ∈ E)
    (x : ℝ) (hx : 0 ≤ x) :
    shb_rhoSupport (shbK4Graph E) x (fun _ ↦ 1) 0 3
        (shbK4DirectPath E h03) =
      shbK4DirectRhoSeries E x := by
  unfold shb_rhoSupport shbK4DirectRhoSeries
  rw [shbK4_backboneNumSupport_eq_seriesMass E h03 x hx,
    shbK4_currentSum_empty_eq_seriesMass E x hx]


theorem shb_supportLex_literal_P3_counterexample :
    shb_rhoSupport (shbK4Graph shbK4H) (Real.artanh (2 / 3))
        (fun _ ↦ 1) 0 3 (shbK4DirectPath shbK4H (by decide)) <
      shb_rhoSupport (shbK4Graph shbK4G) (Real.artanh (2 / 3))
        (fun _ ↦ 1) 0 3
        (shb_pathMapLe (shbK4Graph_mono shbK4H_subset_shbK4G)
          (shbK4DirectPath shbK4H (by decide))) := by
  have hx : 0 ≤ Real.artanh (2 / 3) :=
    Real.artanh_nonneg (by norm_num)
  rw [shbK4DirectPath_mapLe,
    shbK4_rhoSupport_eq_directRhoSeries shbK4H (by decide) _ hx,
    shbK4_rhoSupport_eq_directRhoSeries shbK4G (by decide) _ hx]
  exact shb_supportLex_series_P3_counterexample

end StatMech.Sharpness
