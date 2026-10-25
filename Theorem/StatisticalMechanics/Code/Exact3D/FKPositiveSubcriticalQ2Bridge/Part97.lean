/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part99
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositive_componentSumAbsorption
    (hpos :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical)
    (hsum :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hpos β hβpos hβc, hsum β hβpos hβc] with n hnpos hnsum
  intro H hH Ω v hv
  exact ⟨hnpos H hH v hv, hnsum H hH Ω v hv⟩


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveCurrentWitness_componentSumAbsorption
    (hpos :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitnessPositiveSubcritical)
    (hsum :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositive_componentSumAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveCurrentWitness
      hpos)
    hsum


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveSupportCurrentWitness_componentSumAbsorption
    (hpos :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitnessPositiveSubcritical)
    (hsum :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositive_componentSumAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositive_of_boundaryVertexDenominatorPositiveSupportCurrentWitness
      hpos)
    hsum


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_originalPathWitness3D_componentSumAbsorption
    (hpath : FiniteBoundaryGhostOriginalPathWitness3D)
    (hsum :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveSupportCurrentWitness_componentSumAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveSupportCurrentWitness_of_originalPathWitness3D
      hpath)
    hsum


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let cap :=
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
      n Ωnz
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with ⟨hDpos, hsum⟩
  let oneComponent :=
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n
  let boundaryPairComponent :=
    cap *
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm β H n v
  let emptyBoundaryComponent :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v
  refine
    ⟨oneComponent / D, boundaryPairComponent / D,
      emptyBoundaryComponent / D, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcap : 0 ≤ cap := by
      dsimp [cap, Ωnz]
      exact
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg
          (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω)
    have hone :
        0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH)
    exact div_nonneg (mul_nonneg hcap hone) (le_of_lt hDpos)
  · have hcap : 0 ≤ cap := by
      dsimp [cap, Ωnz]
      exact
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap_nonneg
          (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω)
    have hboundary :
        0 ≤
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH) v
    exact div_nonneg (mul_nonneg hcap hboundary) (le_of_lt hDpos)
  · have hempty :
        0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
          β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH) v
    exact div_nonneg hempty (le_of_lt hDpos)
  · calc
      oneComponent / D + boundaryPairComponent / D +
          emptyBoundaryComponent / D =
          (oneComponent + boundaryPairComponent + emptyBoundaryComponent) /
            D := by
        ring
      _ ≤ D / D := div_le_div_of_nonneg_right hsum (le_of_lt hDpos)
      _ = 1 := div_self hDpos.ne'
  · dsimp [oneComponent]
    rw [div_mul_cancel₀ _ hDpos.ne']
  · dsimp [boundaryPairComponent]
    rw [div_mul_cancel₀ _ hDpos.ne']
  · dsimp [emptyBoundaryComponent]
    rw [div_mul_cancel₀ _ hDpos.ne']


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let D := finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v
  rcases hn H hH Ω v hv with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare,
      _honeShare, _hboundaryShare, _hemptyShare, hshareSum,
      hone, hboundary, hempty⟩
  refine
    ⟨oneShare * D, boundaryPairShare * D, emptyBoundaryShare * D,
      hone, hboundary, hempty, ?_⟩
  have hD : 0 ≤ D := by
    dsimp [D]
    exact finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct_nonneg
      (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH) v
  calc
    oneShare * D + boundaryPairShare * D + emptyBoundaryShare * D =
        (oneShare + boundaryPairShare + emptyBoundaryShare) * D := by
      ring
    _ ≤ 1 * D := mul_le_mul_of_nonneg_right hshareSum hD
    _ = D := by
      ring


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨oneBudget, boundaryPairBudget, emptyBoundaryBudget,
      hone, hboundary, hempty, htotal⟩
  refine ⟨oneBudget, boundaryPairBudget, emptyBoundaryBudget, ?_, ?_, hempty, htotal⟩
  · have hcap :
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω ≤
          finiteBoundaryGhostCollapsedCutoffBoundaryFiberDecrementImageMultiplicityCap
            n Ω :=
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_decrementImageMultiplicityCap
        Ω
    have hone_nonneg :
        0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH)
    exact
      (mul_le_mul_of_nonneg_right hcap hone_nonneg).trans hone
  · have hcap :
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω ≤
          finiteBoundaryGhostCollapsedCutoffBoundaryFiberDecrementImageMultiplicityCap
            n Ω :=
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_decrementImageMultiplicityCap
        Ω
    have hboundary_nonneg :
        0 ≤
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH) v
    exact
      (mul_le_mul_of_nonneg_right hcap hboundary_nonneg).trans hboundary


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with
    ⟨oneBudget, boundaryPairBudget, emptyBoundaryBudget,
      hone, hboundary, hempty, htotal⟩
  refine ⟨oneBudget, boundaryPairBudget, emptyBoundaryBudget, ?_, ?_, hempty, htotal⟩
  · have hcap :
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω ≤
          finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
            n Ω :=
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_sourceSectorMultiplicityCap
        Ω
    have hone_nonneg :
        0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH)
    exact
      (mul_le_mul_of_nonneg_right hcap hone_nonneg).trans hone
  · have hcap :
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω ≤
          finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
            n Ω :=
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_sourceSectorMultiplicityCap
        Ω
    have hboundary_nonneg :
        0 ≤
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH) v
    exact
      (mul_le_mul_of_nonneg_right hcap hboundary_nonneg).trans hboundary


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  refine
    ⟨finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap n Ω,
      ?_, ?_⟩
  · intro v _hv
    exact finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairCap
      Ω v
  · intro v hv
    exact hn H hH Ω v hv


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨oneBudget, boundaryPairBudget, emptyBoundaryBudget,
      hone, hboundary, hempty, htotal⟩
  have hcap :
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ωnz v ≤
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
          n Ωnz :=
    (finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard_le_crossingPairCap
      Ωnz v).trans
      (finiteBoundaryGhostCollapsedCutoffBoundaryFiberCrossingPairCap_le_sourceSectorMultiplicityCap
        Ωnz)
  have hmain :
      0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_nonneg
      (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH) v
  calc
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v =
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ωnz v *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
              β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty
        β H n Ωnz v
    _ ≤
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
            n Ωnz *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
      exact add_le_add (mul_le_mul_of_nonneg_right hcap hmain) le_rfl
    _ =
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
            n Ωnz *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm β H n +
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
            n Ωnz *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
      rw [
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_eq_onePoint_add_boundaryPair]
      ring
    _ ≤ oneBudget + boundaryPairBudget + emptyBoundaryBudget := by
      exact add_le_add (add_le_add hone hboundary) hempty
    _ ≤ finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v :=
      htotal


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  rcases hn H hH Ω v hv with
    ⟨oneBudget, boundaryPairBudget, emptyBoundaryBudget,
      hone, hboundary, hempty, htotal⟩
  have hcap :
      finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap
          n Ωnz ≤
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberBoundaryCrossingPairCountMultiplicityCap
          n Ωnz :=
    finiteBoundaryGhostCollapsedCutoffBoundaryFiberSourceSectorMultiplicityCap_le_boundaryCrossingPairCountMultiplicityCap_weightNonzeroCutoff
      (β := β) (H := H) Ω
  refine ⟨oneBudget, boundaryPairBudget, emptyBoundaryBudget, ?_, ?_, hempty, htotal⟩
  · have hone_nonneg :
        0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH)
    exact
      (mul_le_mul_of_nonneg_right hcap hone_nonneg).trans hone
  · have hboundary_nonneg :
        0 ≤
          finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
            β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm_nonneg
        (le_of_lt hβpos) (le_of_lt hH) v
    exact
      (mul_le_mul_of_nonneg_right hcap hboundary_nonneg).trans hboundary


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  rcases hn H hH Ω with ⟨cap, hcap, hbudget⟩
  refine ⟨cap, hcap, ?_⟩
  intro v hv
  rcases hbudget v hv with
    ⟨oneBudget, boundaryPairBudget, emptyBoundaryBudget,
      hone, hboundary, hempty, htotal⟩
  calc
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v =
      cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
        cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm
          β H n v := by
      rw [
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_eq_onePoint_add_boundaryPair]
      ring
    _ ≤ oneBudget + boundaryPairBudget + emptyBoundaryBudget := by
      exact add_le_add (add_le_add hone hboundary) hempty
    _ ≤ finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v :=
      htotal


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberUniformCardCapAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  rcases hn H hH Ω with ⟨cap, hcap, hcapAbsorb⟩
  refine ⟨cap, hcap, ?_⟩
  intro v hv
  refine
    ⟨cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
        β H n,
      cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
        β H n v,
      finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v,
      le_rfl, le_rfl, le_rfl, ?_⟩
  calc
    cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexOnePointTerm
          β H n +
        cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexBoundaryPairTerm
          β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v =
      cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
      rw [
        finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_eq_onePoint_add_boundaryPair]
      ring
    _ ≤ finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v :=
      hcapAbsorb v hv


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberUniformCardCapAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω with ⟨cap, hcard, habsorb⟩
  exact ⟨cap, hcard v hv, habsorb v hv⟩


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberUniformCardCapAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberUniformCardCapAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberUniformCardCapAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberCardCapAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  rcases hn H hH Ω v hv with ⟨cap, hcap, hcapAbsorb⟩
  have hmain :
      0 ≤ finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm_nonneg
      (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH) v
  calc
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ω v =
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ω v *
            finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v :=
      finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty
        β H n Ω v
    _ ≤
        cap * finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v +
          finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
      exact add_le_add (mul_le_mul_of_nonneg_right hcap hmain) le_rfl
    _ ≤ finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v :=
      hcapAbsorb


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  classical
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  calc
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n Ω ≤
        ∑ v ∈ B,
          finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
      unfold finiteBoundaryGhostBoundaryFiberSourcePairProfile
      refine Finset.sum_le_sum ?_
      intro v hv
      simpa [B] using
        hn H hH Ω v hv
    _ =
        finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n :=
      (finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_boundary_sum_vertexProduct
        β H n).symm


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  classical
  let B : Finset (FK.boxVerts 3 n) :=
    Finset.univ.filter (fun v : FK.boxVerts 3 n => FK.boxBoundary 3 n v)
  calc
    finiteBoundaryGhostBoundaryFiberSourcePairProfile β H n
        (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) ≤
        ∑ v ∈ B,
          finiteBoundaryGhostSimonCollapsedBoundaryVertexProduct β H n v := by
      unfold finiteBoundaryGhostBoundaryFiberSourcePairProfile
      refine Finset.sum_le_sum ?_
      intro v hv
      simpa [B] using
        hn H hH Ω v hv
    _ =
        finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n :=
      (finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_boundary_sum_vertexProduct
        β H n).symm


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairProfileAbsorption
      (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberSourcePairAbsorption
        h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffSourcePairAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberCardCapAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberCardCapAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberUniformCardCapAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberCardCapAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberUniformCardCapAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCardCapAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberCardCapAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorption_of_boundaryFiberUniformCardCapAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberUniformCardCapAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCardCapAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorption_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorption_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffSourcePairAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourceSectorMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapCappedComponentBudgetAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentShareAbsorption_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryVertexDenominatorPositive_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorption
    (hpos :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositivePositiveSubcritical)
    (hsum :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositive_componentSumAbsorption
      hpos hsum)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryVertexDenominatorPositiveCurrentWitness_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorption
    (hpos :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberBoundaryVertexDenominatorPositiveCurrentWitnessPositiveSubcritical)
    (hsum :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapComponentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffBoundaryCrossingPairCountMultiplicityCapPositiveDenominatorComponentSumAbsorption_of_boundaryVertexDenominatorPositiveCurrentWitness_componentSumAbsorption
      hpos hsum)


end Exact3D
end StatMech
