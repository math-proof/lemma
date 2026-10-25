/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardRectilinearFormal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearDeletion.Part2
import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalMultiaffine
import Def.StatisticalMechanics.Code.FrontierA.KacWardRectilinearFormal.Part5
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Onsager


theorem kw_MvSeriesEvalSummable_GraphFormalSecondDifference
    {V : Type*} [DecidableEq V]
    (series : MvPowerSeries (Sym2 V) ℂ) (edge : Sym2 V)
    (weight : Sym2 V → ℂ)
    (h2 : ons_MvSeriesEvalSummable series
      (kwScaleGraphEdgeWeight weight edge 2))
    (h1 : ons_MvSeriesEvalSummable series weight)
    (h0 : ons_MvSeriesEvalSummable series
      (kwScaleGraphEdgeWeight weight edge 0)) :
    ons_MvSeriesEvalSummable
      (kwGraphFormalSecondDifference series edge) weight := by
  let term2 := fun m : Sym2 V →₀ ℕ ↦
    ‖MvPowerSeries.coeff m series *
      ons_mvMonomialValue (kwScaleGraphEdgeWeight weight edge 2) m‖
  let term1 := fun m : Sym2 V →₀ ℕ ↦
    2 * ‖MvPowerSeries.coeff m series * ons_mvMonomialValue weight m‖
  let term0 := fun m : Sym2 V →₀ ℕ ↦
    ‖MvPowerSeries.coeff m series *
      ons_mvMonomialValue (kwScaleGraphEdgeWeight weight edge 0) m‖
  have hs2 : Summable term2 := h2
  have hs1 : Summable term1 := h1.mul_left 2
  have hs0 : Summable term0 := h0
  apply Summable.of_nonneg_of_le (fun m ↦ norm_nonneg _)
    (fun m ↦ ?_) ((hs2.add hs1).add hs0)
  unfold kwGraphFormalSecondDifference ons_secondDifferenceFactor
  simp only [MvPowerSeries.coeff_apply, term2, term1, term0]
  rw [kw_mvMonomialValue_scaleGraphEdgeWeight,
    kw_mvMonomialValue_scaleGraphEdgeWeight]
  let A := (2 : ℂ) ^ m edge * MvPowerSeries.coeff m series *
    ons_mvMonomialValue weight m
  let B := 2 * (MvPowerSeries.coeff m series *
    ons_mvMonomialValue weight m)
  let C := (0 : ℂ) ^ m edge * MvPowerSeries.coeff m series *
    ons_mvMonomialValue weight m
  calc
    ‖((2 : ℂ) ^ m edge - 2 + (0 : ℂ) ^ m edge) *
        MvPowerSeries.coeff m series * ons_mvMonomialValue weight m‖ ≤
      ‖A‖ + ‖B‖ + ‖C‖ := by
      have heq : ((2 : ℂ) ^ m edge - 2 + (0 : ℂ) ^ m edge) *
          MvPowerSeries.coeff m series * ons_mvMonomialValue weight m =
        A - B + C := by simp only [A, B, C]; ring
      rw [heq]
      nlinarith [norm_add_le (A - B) C, norm_sub_le A B]
    _ = _ := by
      simp only [A, B, C, norm_mul, MvPowerSeries.coeff_apply]
      norm_num
      ring

theorem kw_mvSeriesEval_GraphFormalSecondDifference
    {V : Type*} [DecidableEq V]
    (series : MvPowerSeries (Sym2 V) ℂ) (edge : Sym2 V)
    (weight : Sym2 V → ℂ)
    (h2 : ons_MvSeriesEvalSummable series
      (kwScaleGraphEdgeWeight weight edge 2))
    (h1 : ons_MvSeriesEvalSummable series weight)
    (h0 : ons_MvSeriesEvalSummable series
      (kwScaleGraphEdgeWeight weight edge 0)) :
    ons_mvSeriesEval (kwGraphFormalSecondDifference series edge) weight =
      ons_mvSeriesEval series (kwScaleGraphEdgeWeight weight edge 2) -
        2 * ons_mvSeriesEval series weight +
        ons_mvSeriesEval series
          (kwScaleGraphEdgeWeight weight edge 0) := by
  let f2 := fun m : Sym2 V →₀ ℕ ↦
    MvPowerSeries.coeff m series *
      ons_mvMonomialValue (kwScaleGraphEdgeWeight weight edge 2) m
  let f1 := fun m : Sym2 V →₀ ℕ ↦
    MvPowerSeries.coeff m series * ons_mvMonomialValue weight m
  let f0 := fun m : Sym2 V →₀ ℕ ↦
    MvPowerSeries.coeff m series *
      ons_mvMonomialValue (kwScaleGraphEdgeWeight weight edge 0) m
  have hs2 : Summable f2 := Summable.of_norm h2
  have hs1 : Summable f1 := Summable.of_norm h1
  have hs0 : Summable f0 := Summable.of_norm h0
  unfold ons_mvSeriesEval kwGraphFormalSecondDifference
  simp only [MvPowerSeries.coeff_apply]
  have hterm : ∀ m : Sym2 V →₀ ℕ,
      ons_secondDifferenceFactor (m edge) *
          MvPowerSeries.coeff m series * ons_mvMonomialValue weight m =
        f2 m - 2 * f1 m + f0 m := by
    intro m
    rw [show f2 m = (2 : ℂ) ^ m edge *
        MvPowerSeries.coeff m series * ons_mvMonomialValue weight m by
      simp only [f2, kw_mvMonomialValue_scaleGraphEdgeWeight]; ring,
      show f0 m = (0 : ℂ) ^ m edge *
        MvPowerSeries.coeff m series * ons_mvMonomialValue weight m by
      simp only [f0, kw_mvMonomialValue_scaleGraphEdgeWeight]; ring]
    simp only [f1, ons_secondDifferenceFactor]
    ring
  change (∑' m, ons_secondDifferenceFactor (m edge) *
      MvPowerSeries.coeff m series * ons_mvMonomialValue weight m) =
    (∑' m, f2 m) - 2 * (∑' m, f1 m) + ∑' m, f0 m
  rw [tsum_congr hterm, (hs2.sub (hs1.mul_left 2)).tsum_add hs0,
    hs2.tsum_sub (hs1.mul_left 2), tsum_mul_left]

@[simp] theorem kwScaleGraphEdgeWeight_one
    {V : Type*} [DecidableEq V]
    (weight : Sym2 V → ℂ) (edge : Sym2 V) :
    kwScaleGraphEdgeWeight weight edge 1 = weight := by
  funext other
  simp [kwScaleGraphEdgeWeight]

theorem kwGraphTransition_smulWeight
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (c : ℂ) (dart next : G.Dart) :
    kwGraphTransition G (fun edge ↦ c * weight edge) phase dart next =
      c * kwGraphTransition G weight phase dart next := by
  unfold kwGraphTransition
  split
  · ring
  · simp

theorem norm_kwGraphTransition_scaleEdge_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (weight : Sym2 V → ℂ) (phase : G.Dart → G.Dart → ℂ)
    (selected : G.Dart) (t : ℂ) (r : ℝ) (hr : 0 ≤ r)
    (ht : ‖t‖ ≤ 2)
    (hentry : ∀ dart next,
      ‖kwGraphTransition G weight phase dart next‖ ≤ r)
    (dart next : G.Dart) :
    ‖kwGraphTransition G
      (kwScaleGraphEdgeWeight weight selected.edge t) phase dart next‖ ≤
        2 * r := by
  rw [kwGraphTransition_scaleEdge_entry, norm_mul]
  by_cases hedge : dart.edge = selected.edge
  · rw [if_pos hedge]
    nlinarith [mul_le_mul ht (hentry dart next)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  · rw [if_neg hedge]
    norm_num
    linarith [hentry dart next]

theorem norm_kwScaleColumns_le
    {E : Type*} [DecidableEq E]
    (S : Finset E) (t : ℂ) (M : Matrix E E ℂ)
    (r : ℝ) (hr : 0 ≤ r) (ht : ‖t‖ ≤ 2)
    (hentry : ∀ i j, ‖M i j‖ ≤ r) (i j : E) :
    ‖ons_scaleColumns S t M i j‖ ≤ 2 * r := by
  unfold ons_scaleColumns
  by_cases hj : j ∈ S
  · rw [if_pos hj, norm_mul]
    nlinarith [mul_le_mul ht (hentry i j)
      (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)]
  · rw [if_neg hj]
    linarith [hentry i j]


theorem kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (direction : G.Dart → Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (selected : G.Dart) (m : Sym2 V →₀ ℕ)
    (hrepeated : 2 ≤ m selected.edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G (fun dart next ↦
        ons_turnW omega (direction next) (direction dart))) = 0 := by
  letI : Nonempty G.Dart := ⟨selected⟩
  let phase := fun dart next : G.Dart ↦
    ons_turnW omega (direction next) (direction dart)
  let root := kwGraphFormalRoot G phase
  let second := kwGraphFormalSecondDifference root selected.edge
  have hsecond : MvPowerSeries.coeff m second = 0 := by
    apply ons_coeff_eq_zero_of_degreeFiberCoeff second m
    intro weight
    let radius : ℝ := (2 * (Fintype.card G.Dart : ℝ) ^ 2)⁻¹
    let R : ℝ := min 1 radius
    let r : ℝ := R / 4
    let q : ℝ := 2 * r
    let S : ℝ := ∑ dart : G.Dart, ∑ next : G.Dart,
      ‖kwGraphTransition G weight phase dart next‖
    let c : ℂ := ((r / (1 + S) : ℝ) : ℂ)
    let base : Sym2 V → ℂ := fun edge ↦ c * weight edge
    have hradius : 0 < radius := by
      dsimp only [radius]
      positivity
    have hR : 0 < R := by
      dsimp only [R]
      exact lt_min (by norm_num) hradius
    have hRradius : R ≤ radius := min_le_right _ _
    have hr : 0 < r := by dsimp only [r]; linarith
    have hq : 0 < q := by dsimp only [q]; linarith
    have hsmall : q < radius := by
      dsimp only [q, r]
      linarith
    have hcard : (Fintype.card G.Dart : ℝ) * q < 1 :=
      ons_card_mul_lt_one_of_Sherman_small q hsmall
    have hS : 0 ≤ S := by
      dsimp only [S]
      exact Finset.sum_nonneg fun _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    have hden : 0 < 1 + S := by linarith
    have hc : c ≠ 0 := by
      dsimp only [c]
      exact_mod_cast div_ne_zero (ne_of_gt hr) (ne_of_gt hden)
    have hraw (dart next : G.Dart) :
        ‖kwGraphTransition G weight phase dart next‖ ≤ S := by
      have hinner :
          ‖kwGraphTransition G weight phase dart next‖ ≤
            ∑ e : G.Dart, ‖kwGraphTransition G weight phase dart e‖ :=
        Finset.single_le_sum
          (fun e _ ↦ norm_nonneg
            (kwGraphTransition G weight phase dart e))
          (Finset.mem_univ next)
      exact hinner.trans <| Finset.single_le_sum
        (fun d _ ↦ Finset.sum_nonneg fun e _ ↦ norm_nonneg
          (kwGraphTransition G weight phase d e))
        (Finset.mem_univ dart)
    have hbase (dart next : G.Dart) :
        ‖kwGraphTransition G base phase dart next‖ ≤ r := by
      rw [show base = fun edge ↦ c * weight edge from rfl,
        kwGraphTransition_smulWeight, norm_mul]
      have hnormc : ‖c‖ = r / (1 + S) := by
        dsimp only [c]
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (div_nonneg hr.le hden.le)]
      rw [hnormc, div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [hraw dart next]
    have hrootSummable (t : ℂ) (ht : ‖t‖ ≤ 2) :
        ons_MvSeriesEvalSummable root
          (kwScaleGraphEdgeWeight base selected.edge t) := by
      apply kw_MvSeriesEvalSummable_GraphFormalRoot
        G phase (kwScaleGraphEdgeWeight base selected.edge t)
          q hq.le
      · intro dart next
        simpa only [q] using norm_kwGraphTransition_scaleEdge_le
          G base phase selected t r hr.le ht hbase dart next
      · exact hcard
    have hsumSecond : ons_MvSeriesEvalSummable second base := by
      apply kw_MvSeriesEvalSummable_GraphFormalSecondDifference
      · exact hrootSummable 2 (by norm_num)
      · simpa only [kwScaleGraphEdgeWeight_one] using
          hrootSummable 1 (by norm_num)
      · exact hrootSummable 0 (by norm_num)
    have hzero : ∀ᶠ s : ℂ in nhds 0,
        ons_mvSeriesEval second (fun edge ↦ s * base edge) = 0 := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ)
        (by norm_num : (0 : ℝ) < 1)] with s hs
      have hs1 : ‖s‖ ≤ 1 := by
        have : ‖s‖ < 1 := by
          simpa only [Metric.mem_ball, dist_zero_right] using hs
        exact this.le
      let scaled : Sym2 V → ℂ := fun edge ↦ s * base edge
      have hscaled (dart next : G.Dart) :
          ‖kwGraphTransition G scaled phase dart next‖ ≤ r := by
        rw [show scaled = fun edge ↦ s * base edge from rfl,
          kwGraphTransition_smulWeight, norm_mul]
        calc
          ‖s‖ * ‖kwGraphTransition G base phase dart next‖ ≤
              1 * r := mul_le_mul hs1 (hbase dart next)
                (norm_nonneg _) (by norm_num)
          _ = r := one_mul r
      have hsum (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_MvSeriesEvalSummable root
            (kwScaleGraphEdgeWeight scaled selected.edge t) := by
        apply kw_MvSeriesEvalSummable_GraphFormalRoot
          G phase (kwScaleGraphEdgeWeight scaled selected.edge t)
            q hq.le
        · intro dart next
          simpa only [q] using norm_kwGraphTransition_scaleEdge_le
            G scaled phase selected t r hr.le ht hscaled dart next
        · exact hcard
      have heval (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_mvSeriesEval root
              (kwScaleGraphEdgeWeight scaled selected.edge t) =
            ons_detWalkRoot
              (kwGraphTransition G
                (kwScaleGraphEdgeWeight scaled selected.edge t) phase) := by
        apply kw_mvSeriesEval_GraphFormalRoot
          G phase (kwScaleGraphEdgeWeight scaled selected.edge t)
            q hq.le
        · intro dart next
          simpa only [q] using norm_kwGraphTransition_scaleEdge_le
            G scaled phase selected t r hr.le ht hscaled dart next
        · exact hcard
      let A := ons_detWalkRoot
        (ons_maskMatrix ({selected, selected.symm} : Finset G.Dart)
          (kwGraphTransition G scaled phase))
      let B := ∑' path, ons_firstReturnWeight
        (kwGraphTransition G scaled phase) selected selected.symm path
      have haff (t : ℂ) (ht : ‖t‖ ≤ 2) :
          ons_detWalkRoot
              (kwGraphTransition G
                (kwScaleGraphEdgeWeight scaled selected.edge t) phase) =
            A * (1 - t * B) := by
        apply kw_rectilinearGraph_detWalkRoot_scaleEdge_affine
          G scaled direction hdirection omega homega homega_sq
            selected t q hq.le
        · intro dart next
          simpa only [q] using norm_kwScaleColumns_le
            ({selected, selected.symm} : Finset G.Dart) t
            (kwGraphTransition G scaled phase) r hr.le ht hscaled dart next
        · exact hsmall
        · exact hcard
      have hscaleOne :
          kwScaleGraphEdgeWeight scaled selected.edge 1 = scaled :=
        kwScaleGraphEdgeWeight_one scaled selected.edge
      rw [kw_mvSeriesEval_GraphFormalSecondDifference
        root selected.edge scaled
        (hsum 2 (by norm_num))
        (by simpa only [hscaleOne] using hsum 1 (by norm_num))
        (hsum 0 (by norm_num))]
      rw [heval 2 (by norm_num)]
      have heval1 : ons_mvSeriesEval root scaled =
          ons_detWalkRoot (kwGraphTransition G scaled phase) := by
        simpa only [hscaleOne] using heval 1 (by norm_num)
      have haff1 : ons_detWalkRoot (kwGraphTransition G scaled phase) =
          A * (1 - B) := by
        simpa only [hscaleOne, one_mul] using haff 1 (by norm_num)
      rw [heval1, heval 0 (by norm_num),
        haff 2 (by norm_num), haff1,
        haff 0 (by norm_num)]
      ring
    have hfiber :=
      ons_degreeFiberCoeff_eq_zero_of_eval_smul_eventually_zero
        second base hsumSecond hzero (Finsupp.degree m)
    change ons_degreeFiberCoeff second
      (fun edge ↦ c * weight edge) (Finsupp.degree m) = 0 at hfiber
    rw [ons_degreeFiberCoeff_scale] at hfiber
    exact (mul_eq_zero.mp hfiber).resolve_left (pow_ne_zero _ hc)
  change ons_secondDifferenceFactor (m selected.edge) *
      MvPowerSeries.coeff m root = 0 at hsecond
  exact (mul_eq_zero.mp hsecond).resolve_left
    (ons_secondDifferenceFactor_ne_zero (m selected.edge) hrepeated)


theorem kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated_edge
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (direction : G.Dart → Fin 4)
    (hdirection : ∀ dart, direction dart.symm = direction dart + 2)
    (omega : ℂ) (homega : omega ≠ 0)
    (homega_sq : omega ^ 2 = Complex.I)
    (edge : Sym2 V) (hedge : edge ∈ G.edgeFinset)
    (m : Sym2 V →₀ ℕ) (hrepeated : 2 ≤ m edge) :
    MvPowerSeries.coeff m
      (kwGraphFormalRoot G (fun dart next ↦
        ons_turnW omega (direction next) (direction dart))) = 0 := by
  rw [SimpleGraph.mem_edgeFinset] at hedge
  obtain ⟨v, w⟩ := edge
  let selected : G.Dart := ⟨(v, w), hedge⟩
  exact kw_rectilinearGraph_formalRoot_coeff_eq_zero_of_repeated
    G direction hdirection omega homega homega_sq selected m hrepeated

end StatMech.FrontierA
