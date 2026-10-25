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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part97
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorption_of_componentShareAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  rcases hn H hH Ω with
    ⟨oneShare, boundaryPairShare, emptyBoundaryShare,
      _honeShare, _hboundaryShare, _hemptyShare, hshareSum,
      hone, hboundary, hempty⟩
  let D :=
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator
      β H n
  refine
    ⟨oneShare * D, boundaryPairShare * D, emptyBoundaryShare * D,
      hone, hboundary, hempty, ?_⟩
  have hD : 0 ≤ D := by
    dsimp [D]
    exact
      finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator_nonneg
        (β := β) (H := H) (n := n) (le_of_lt hβpos) (le_of_lt hH)
  have hbudgetD :
      oneShare * D + boundaryPairShare * D + emptyBoundaryShare * D ≤ D := by
    calc
      oneShare * D + boundaryPairShare * D + emptyBoundaryShare * D =
          (oneShare + boundaryPairShare + emptyBoundaryShare) * D := by
        ring
      _ ≤ 1 * D := mul_le_mul_of_nonneg_right hshareSum hD
      _ = D := by
        ring
  simpa [
    D,
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardCurrentDenominator]
    using hbudgetD


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorption_of_componentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  rcases hn H hH Ω with
    ⟨oneBudget, boundaryPairBudget, emptyBoundaryBudget,
      hone, hboundary, hempty, hbudget⟩
  calc
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound
        β H n Ω =
      finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardOnePointCurrentComponent
          β H n Ω +
        finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardBoundaryPairCurrentComponent
          β H n Ω +
        finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardEmptyBoundaryCurrentComponent
          β H n Ω :=
      finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound_eq_components
        β H n Ω
    _ ≤ oneBudget + boundaryPairBudget + emptyBoundaryBudget := by
      exact add_le_add (add_le_add hone hboundary) hempty
    _ ≤
      finiteCurrentBoundaryTwoPointSum β n *
        (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n))) *
        Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n)))) :=
      hbudget


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorption_of_componentShareAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorption_of_componentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorption_of_componentShareAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorption_of_currentSumAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  calc
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound
        β H n Ω ≤
      finiteCurrentBoundaryTwoPointSum β n *
        (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n))) *
        Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n)))) :=
      hn H hH Ω
    _ =
        finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n :=
      (finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_currentSum_empty_sq
        β H n).symm


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorption_of_currentAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  calc
    finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound
        β H n Ω =
      finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairCurrentBound
        β H n Ω :=
      finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound_eq_currentBound
        β H n Ω
    _ ≤
        finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct β H n :=
      hn H hH Ω


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorption_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  have hTpos : 0 < Real.tanh (β * H) :=
    real_tanh_pos_of_pos (mul_pos hβpos hH)
  have hTne : Real.tanh (β * H) ≠ 0 := ne_of_gt hTpos
  calc
    finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound β H n Ω =
        Real.tanh (β * H) *
          finiteBoundaryGhostTanhNormalizedBoundaryFiberImageCardSourcePairBound
            β H n Ω :=
      finiteBoundaryGhostBoundaryFiberImageCardSourcePairBound_eq_tanh_mul_normalized
        Ω hTne
    _ ≤
        Real.tanh (β * H) *
          finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct
            β H n :=
      mul_le_mul_of_nonneg_left (hn H hH Ω) (le_of_lt hTpos)
    _ =
        finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n :=
      (finiteBoundaryGhostSimonCollapsedDenominatorProduct_eq_tanh_mul_normalized
        β H n).symm


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberImageCardSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  exact
      finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_imageCardSourcePairBound
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ω
        (hn H hH Ω)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberDecomposedSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecomposedSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  exact
    finiteBoundaryGhostBoundaryFiberSourcePairProfile_le_denominatorProduct_of_decomposedSourcePairBound
      β H Ω (hn H hH Ω)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairProfileAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  exact
      (finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairProfile
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ω).trans
      (hn H hH Ω)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairProfileAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  exact
      (finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_boundaryFiberSourcePairProfile_weightNonzeroCutoff
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ω).trans
      (hn H hH Ω)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberImageCardSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairProfileAbsorption
      (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberImageCardSourcePairAbsorption
        h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberDecomposedSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecomposedSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairProfileAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorption_of_boundaryFiberDecomposedSourcePairAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberImageCardSourcePairAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorption_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorption_of_currentAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorption_of_currentSumAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorption_of_componentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorption_of_componentShareAbsorption
      h)


end Exact3D
end StatMech
