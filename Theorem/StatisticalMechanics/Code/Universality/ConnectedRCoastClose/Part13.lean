/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/ConnectedRCoastClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossing.Part3
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Universality.CrossingReflection.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAllAspect
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.RCoastMengerClose.Part2
import Def.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped NNReal
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crr_faceDualConnectionEvent_eq_preimage (n : ℤ) :
    crr_FaceDualConnectionEvent n =
      fci_faceDualConfig ⁻¹' crr_FaceConnectionEvent n := by
  ext ω
  change pmd_FaceDualVCrossing ω n ↔
    ∃ (a₀ a₁ : ℤ), 0 ≤ a₀ ∧ a₀ ≤ n - 1 ∧ 0 ≤ a₁ ∧ a₁ ≤ n - 1 ∧
      (openSubgraph 2 (fci_faceDualConfig ω)).Reachable ![a₀, -1] ![a₁, n]
  unfold pmd_FaceDualVCrossing
  rw [fci_faceOpenDual_eq_openSubgraph]


theorem crr_faceDualConnection_half_law (n : ℤ)
    (hmeas : MeasurableSet (crr_FaceConnectionEvent n)) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one)
        (crr_FaceDualConnectionEvent n) =
      (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one)
        (crr_FaceConnectionEvent n) := by
  rw [crr_faceDualConnectionEvent_eq_preimage]
  exact fci_faceDualConfig_measurePreserving.measure_preimage hmeas.nullMeasurableSet


theorem crr_square_compl_subset_faceDualConnection (n : ℤ) (hn : 0 ≤ n)
    (horder : ∀ ω : ConfigSpace (Sym2 (Site 2)), crr_LeftFillFrameArcOrder ω n) :
    (horizontalCrossingEvent 0 n 0 n)ᶜ ⊆ crr_FaceDualConnectionEvent n := by
  intro ω hnoH
  exact crr_faceDualVCrossing_of_residue ω n hn hnoH
    (crr_interfaceCoastConnected_of_frameArcOrder ω n (horder ω))


theorem crr_square_half_of_frameArcOrder_and_faceComparison (n : ℤ) (hn : 0 ≤ n)
    (horder : ∀ ω : ConfigSpace (Sym2 (Site 2)), crr_LeftFillFrameArcOrder ω n)
    (hmeasH : MeasurableSet (horizontalCrossingEvent 0 n 0 n))
    (hmeasFace : MeasurableSet (crr_FaceConnectionEvent n))
    (hcompare :
      (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one).real
          (crr_FaceConnectionEvent n) ≤
        (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one).real
          (horizontalCrossingEvent 0 n 0 n)) :
    (1 : ℝ) / 2 ≤
      (bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one).real
        (horizontalCrossingEvent 0 n 0 n) := by
  let μ := bernoulliProductMeasure (E := Sym2 (Site 2)) (2⁻¹ : ℝ≥0) half_le_one
  have hmono : μ.real (horizontalCrossingEvent 0 n 0 n)ᶜ ≤
      μ.real (crr_FaceDualConnectionEvent n) :=
    measureReal_mono (crr_square_compl_subset_faceDualConnection n hn horder)
  have hlaw : μ.real (crr_FaceDualConnectionEvent n) =
      μ.real (crr_FaceConnectionEvent n) := by
    exact congrArg ENNReal.toReal (crr_faceDualConnection_half_law n hmeasFace)
  rw [measureReal_compl hmeasH, probReal_univ, hlaw] at hmono
  dsimp [μ] at hmono
  linarith


theorem crr_faceDualVCrossing_of_leftFillInteriorArc
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (harc : crr_LeftFillInteriorArc ω n) : pmd_FaceDualVCrossing ω n :=
  crr_faceDualVCrossing_of_residue ω n hn hnoH
    (crr_interfaceCoastConnected_of_leftFillInteriorArc ω n harc)


theorem crr_wall_frameFace_not_pmd_support :
    (![2, 0] : Site 2) ∉ (pmd_boxFaceBarrier bcc_wallCfg 2).support := by
  intro h
  rw [SimpleGraph.mem_support] at h
  obtain ⟨g, hg⟩ := h
  have hcol := bac_wall_barrierFace_col0 hg
  norm_num at hcol


theorem crr_wall_frameEdge_not_pmd_reachable :
    ¬ (pmd_boxFaceBarrier bcc_wallCfg 2).Reachable ![2, 0] ![2, -1] := by
  rintro ⟨w⟩
  have hne : (![2, 0] : Site 2) ≠ ![2, -1] := by
    intro h
    have := congrFun h 1
    norm_num at this
  obtain ⟨b, hab, p, rfl⟩ := w.exists_eq_cons_of_ne hne
  exact crr_wall_frameFace_not_pmd_support hab.mem_support_left

end Universality
end StatMech
