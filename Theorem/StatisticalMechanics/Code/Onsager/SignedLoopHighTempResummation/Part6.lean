/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopHighTempResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part5
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopCanonicalRectShiftedEndpoint.Part3
import Def.StatisticalMechanics.Code.Onsager.SignedLoopHighTempResummation.Part6
open scoped BigOperators
open Finset SimpleGraph MeasureTheory Filter Topology


namespace StatMech.Onsager

open StatMech.FrontierA StatMech.Ising StatMech.Lattice

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem norm_reciprocalInterpolationValue_le
    (q : Real) (hq : 0 ≤ q) (s : Fin 3) :
    ‖ons_reciprocalInterpolationValue (q : Complex) s‖ ≤ q := by
  fin_cases s
  · simp [ons_reciprocalInterpolationValue, hq]
  · simp [ons_reciprocalInterpolationValue, Real.norm_eq_abs,
      abs_of_nonneg hq]
  · simpa [ons_reciprocalInterpolationValue, Real.norm_eq_abs,
      abs_of_nonneg hq] using le_rfl

theorem norm_ons_setGraphEdgeWeight_le
    (weight : Sym2 V → Complex) (edge : Sym2 V) (z : Complex)
    (q : Real) (hweight : ∀ f, ‖weight f‖ ≤ q) (hz : ‖z‖ ≤ q) :
    ∀ f, ‖ons_setGraphEdgeWeight weight edge z f‖ ≤ q := by
  intro f
  by_cases hfe : f = edge
  · subst f
    simpa using hz
  · simpa [ons_setGraphEdgeWeight, hfe] using hweight f


theorem boundedReciprocalRectKWDetResum_eq_walkResum
    (M N : Nat)
    (weight : Sym2 (ons_RectDualVertex M N) → Complex)
    (q : Real) (hq0 : 0 ≤ q) (hq : q < ons_signedLoopCriticalWeight)
    (hweight : ∀ edge, ‖weight edge‖ ≤ q)
    (edges : List (Sym2 (ons_RectDualVertex M N))) :
    ons_boundedReciprocalKWDetResum (ons_rectDualGraph M N)
        (ons_rectDualStraightLineEmbedding M N) weight (q : Complex) edges =
      ons_boundedReciprocalRectWalkResum M N weight (q : Complex) edges := by
  induction edges generalizing weight with
  | nil =>
      simp only [ons_boundedReciprocalKWDetResum,
        ons_boundedReciprocalRectWalkResum]
      exact kwGraphTransition_canonical_det_eq_walk_exp
        M N weight q hq0 hq hweight
  | cons edge edges ih =>
      simp only [ons_boundedReciprocalKWDetResum,
        ons_boundedReciprocalRectWalkResum]
      apply Finset.sum_congr rfl
      intro s hs
      congr 1
      exact ih
        (ons_setGraphEdgeWeight weight edge
          (ons_reciprocalInterpolationValue (q : Complex) s))
        (norm_ons_setGraphEdgeWeight_le _ edge _ q hweight
          (norm_reciprocalInterpolationValue_le q hq0 s))

theorem setGraphEdgeWeightList_uniform_eq_pathDefectWeight
    {M N : Nat} (path : ons_RectDualPath M N) (q : Real) :
    ons_setGraphEdgeWeightList (fun _ ↦ (q : Complex)) (q : Complex)⁻¹
        (ons_rectDualPathDefect path).toList =
      ons_rectDualPathDefectWeight path q := by
  funext edge
  rw [ons_setGraphEdgeWeightList_apply]
  simp [ons_rectDualPathDefectWeight]


theorem rectDualPath_sourceDet_eq_bounded_walkResum
    {M N : Nat} (path : ons_RectDualPath M N)
    (q : Real) (hq0 : 0 < q) (hq : q < ons_signedLoopCriticalWeight) :
    (q : Complex) ^ (2 * (ons_rectDualPathDefect path).card) *
        ons_rectDualPathCanonicalDefectKWDet path q =
      ons_boundedReciprocalRectWalkResum M N
        (fun _ ↦ (q : Complex)) (q : Complex)
        (ons_rectDualPathDefect path).toList := by
  have hqne : (q : Complex) ≠ 0 := by exact_mod_cast hq0.ne'
  have hinterp := reciprocalKWDet_list_eq_bounded_resum
    (ons_rectDualGraph M N) (ons_rectDualStraightLineEmbedding M N)
    (fun _ ↦ (q : Complex)) (q : Complex) hqne
    (ons_rectDualPathDefect path).toList
    (Finset.nodup_toList (ons_rectDualPathDefect path))
  rw [Finset.length_toList,
    setGraphEdgeWeightList_uniform_eq_pathDefectWeight path q] at hinterp
  have hwalk := boundedReciprocalRectKWDetResum_eq_walkResum
    M N (fun _ ↦ (q : Complex)) q hq0.le hq
    (fun _ ↦ by
      simp [Real.norm_eq_abs, abs_of_pos hq0])
    (ons_rectDualPathDefect path).toList
  rw [← hwalk]
  simpa [ons_rectDualPathCanonicalDefectKWDet,
    ons_rectDualPathDefectKWDet] using hinterp


theorem coe_rectDualPath_finiteTwoPoint_sq_eq_bounded_walkResum
    {M N : Nat} (path : ons_RectDualPath M N)
    (beta : Real) (hbeta0 : 0 < beta) (hbetaC : beta < ons_betaC) :
    (StatMech.Ising.isingExpectation (ons_rectDualGraph M N) beta 0
        (fun spin ↦ StatMech.Ising.spin spin path.source *
          StatMech.Ising.spin spin path.target) : Complex) ^ 2 =
      ons_boundedReciprocalRectWalkResum M N
          (fun _ ↦ (Real.tanh beta : Complex))
          (Real.tanh beta : Complex)
          (ons_rectDualPathDefect path).toList /
        Complex.exp (-(ons_rectDualWalkExponent M N
          (fun _ ↦ (Real.tanh beta : Complex)))) := by
  let q := Real.tanh beta
  have hq0 : 0 < q := by
    dsimp only [q]
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hbeta0) (Real.cosh_pos beta)
  have hqcrit : q < ons_signedLoopCriticalWeight :=
    tanh_lt_signedLoopCriticalWeight hbetaC
  have hsource := rectDualPath_sourceDet_eq_bounded_walkResum
    path q hq0 hqcrit
  have hplain := kwGraphTransition_canonical_det_eq_walk_exp
    M N (fun _ ↦ (q : Complex)) q hq0.le hqcrit
    (fun _ ↦ by simp [Real.norm_eq_abs, abs_of_pos hq0])
  rw [coe_ons_rectDualPath_finiteTwoPoint_sq_eq_canonicalKWDet_ratio
    path hbeta0]
  change ((q : Complex) ^ (2 * (ons_rectDualPathDefect path).card) *
      ons_rectDualPathCanonicalDefectKWDet path q) /
        ons_rectDualCanonicalKWDet M N q = _
  rw [hsource]
  change _ / (1 - kwGraphTransition (ons_rectDualGraph M N)
    (fun _ ↦ (q : Complex))
    (ons_rectDualStraightLineEmbedding M N).turnPhase).det = _
  rw [hplain]
  rfl


end
end StatMech.Onsager
