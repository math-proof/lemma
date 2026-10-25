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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part100
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteTanhNormalizedAbsorption_of_currentAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteTanhNormalizedCurrentAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteTanhNormalizedAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  calc
    finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile
        β H n Ω =
      finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCurrentProfile
        β H n Ω :=
      finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile_eq_currentProfile
        β H n Ω
    _ ≤
      finiteCurrentBoundaryTwoPointSum β n *
        (Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n))) *
        Sharpness.currentSum (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) H (fun _ => 1))
          (∅ : Finset (Option (FK.boxVerts 3 n)))) :=
      hn H hH Ω
    _ =
      finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct
        β H n :=
      (finiteBoundaryGhostTanhNormalizedSimonCollapsedDenominatorProduct_eq_finiteCurrentBoundaryTwoPointSum_mul_currentSum_empty_sq
        β H n).symm


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryMultiplicityAbsorption_of_tanhNormalizedAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteTanhNormalizedAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryMultiplicityAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  have hTpos : 0 < Real.tanh (β * H) :=
    real_tanh_pos_of_pos (mul_pos hβpos hH)
  have hTne : Real.tanh (β * H) ≠ 0 := ne_of_gt hTpos
  calc
    finiteBoundaryGhostCutoffBoundaryMultiplicityCollapsedProfile β H n Ω =
        Real.tanh (β * H) *
          finiteBoundaryGhostTanhNormalizedCutoffBoundaryMultiplicityCollapsedProfile
            β H n Ω :=
      finiteBoundaryGhostCutoffBoundaryMultiplicityCollapsedProfile_eq_tanh_mul_normalized
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
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryMultiplicityAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryMultiplicityAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  exact
    le_trans
      (finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_cutoffBoundaryMultiplicityCollapsedProfile
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ω)
      (hn H hH Ω)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  rw [← finiteBoundaryGhostCollapsedSourceSummand_tsum_eq_emptyCollapsedSum β H n]
  exact
    tsum_le_of_all_finset_sum_le
      (finiteBoundaryGhostCollapsedSourceSummand_summable β H n)
      (fun Ω => by
        simpa [finiteBoundaryGhostSimonCollapsedDenominatorProduct] using
          hn H hH Ω)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_decrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_decrementedSourceAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexDecrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_decrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexSigmaFiniteSubcaseAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_decrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexSigmaFiniteSubcaseAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexSigmaFiniteLabelCaseAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexSigmaFiniteSubcaseAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorption_of_boundaryVertexSigmaFiniteLabelCaseAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_globalDecrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_decrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_globalDecrementedSourceAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_sigmaDecrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_globalDecrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorption_of_sigmaDecrementedSourceAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_sigmaFiniteSubcaseAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_sigmaDecrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorption_of_sigmaFiniteSubcaseAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryMultiplicityAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryMultiplicityAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryMultiplicityAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourcePairProfileAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairProfileAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberImageCardSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
      (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberImageCardSourcePairAbsorption
        h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberDecomposedSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecomposedSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberDecomposedSourcePairAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
      (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourcePairAbsorption
        h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberCardCapAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberCardCapAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberUniformCardCapAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCardCapAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberUniformCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_finiteCutoffBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem finiteBoundaryGhostScalarBound_zeroField
    (β : ℝ) (n : ℕ) :
    Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
      (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1))
      (({some (IsingFK.boxOrigin 3 n)} :
        Finset (Option (FK.boxVerts 3 n))) ∆ {none})
    ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
        finiteBoundaryGhostSimonWeight β (0 : ℝ) n x none := by
  rw [finiteBoundaryGhostExpectation_zeroField_eq_zero]
  rw [finiteBoundaryGhostSimonWeight_sum_zeroField_eq_zero]


theorem finiteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical_H0 :
    ∀ β (_hβpos : 0 < β), β < Ising.betaC 3 →
      ∀ᶠ n in atTop,
        Sharpness.expectationJ (Sharpness.withGhost (FK.boxGraph 3 n)) β
          (boundaryGhostCoupling (FK.boxBoundary 3 n) (0 : ℝ) (fun _ => 1))
          (({some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n))) ∆ {none})
        ≤ ∑ x ∈ finiteBoundaryGhostOriginalSet 3 n,
            finiteBoundaryGhostSimonWeight β (0 : ℝ) n x none := by
  intro β _hβpos _hβc
  exact Eventually.of_forall fun n =>
    finiteBoundaryGhostScalarBound_zeroField β n


theorem finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBound_of_firstExitPositive
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBoundPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  by_cases hHpos : 0 < H
  · exact hn H hHpos
  · have hHzero : H = 0 := le_antisymm (not_lt.mp hHpos) hH
    rw [hHzero]
    exact finiteBoundaryGhostCollapsedEdgeCopyBound_zeroField β n


theorem finiteQ2SimonBoundaryGhostScalarBound_of_scalarCurrentBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarCurrentBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  exact finiteBoundaryGhostScalarBound_of_currentOnePoint (hn H hH)


theorem finiteQ2SimonBoundaryGhostScalarCurrentBound_of_scalarCurrentSumBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarCurrentSumBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCurrentBoundPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  exact finiteBoundaryGhostCurrentOnePoint_le_of_currentSumBound (hn H hH)


theorem finiteQ2SimonBoundaryGhostScalarBound_of_scalarCurrentSumBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarCurrentSumBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarBound_of_scalarCurrentBound
    (finiteQ2SimonBoundaryGhostScalarCurrentBound_of_scalarCurrentSumBound h)


theorem finiteQ2SimonBoundaryGhostScalarCurrentSumBound_of_sourcePairBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarSourcePairBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCurrentSumBoundPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  exact finiteBoundaryGhostCurrentSumBound_of_sourcePairBound (hn H hH)


theorem finiteQ2SimonBoundaryGhostScalarBound_of_sourcePairBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarSourcePairBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarBound_of_scalarCurrentSumBound
    (finiteQ2SimonBoundaryGhostScalarCurrentSumBound_of_sourcePairBound h)


theorem finiteQ2SimonBoundaryGhostScalarSourcePairBound_of_edgeCopyBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarEdgeCopyBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarSourcePairBoundPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  exact finiteBoundaryGhostSourcePairBound_of_edgeCopyBound (hn H hH)


theorem finiteQ2SimonBoundaryGhostScalarBound_of_edgeCopyBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarEdgeCopyBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarBound_of_sourcePairBound
    (finiteQ2SimonBoundaryGhostScalarSourcePairBound_of_edgeCopyBound h)


theorem finiteQ2SimonBoundaryGhostScalarEdgeCopyBound_of_emptyCollapsedBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarEdgeCopyBoundPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  exact finiteBoundaryGhostEdgeCopyBound_of_emptyCollapsedBound (hn H hH)


theorem finiteQ2SimonBoundaryGhostScalarSourcePairBound_of_emptyCollapsedBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarSourcePairBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarSourcePairBound_of_edgeCopyBound
    (finiteQ2SimonBoundaryGhostScalarEdgeCopyBound_of_emptyCollapsedBound h)


theorem finiteQ2SimonBoundaryGhostScalarBound_of_emptyCollapsedBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarBound_of_edgeCopyBound
    (finiteQ2SimonBoundaryGhostScalarEdgeCopyBound_of_emptyCollapsedBound h)


theorem finiteQ2SimonBoundaryGhostScalarEdgeCopyBound_of_firstExitPositive
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarEdgeCopyBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarEdgeCopyBound_of_emptyCollapsedBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBound_of_firstExitPositive h)


theorem finiteQ2SimonBoundaryGhostScalarBound_of_firstExitPositive
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarBound_of_emptyCollapsedBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBound_of_firstExitPositive h)


theorem finiteQ2SimonBoundaryGhostSingletonSimonLieb_of_scalarBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostSingletonSimonLiebPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  exact finiteBoundaryGhostSingletonSimonLieb_of_scalarBound
    (le_of_lt hβpos) hH (hn H hH)


theorem
    finiteQ2SimonBoundaryGhostSingletonSimonLiebLocalization_of_singletonSimonLieb
    (h :
      FiniteQ2SimonBoundaryGhostSingletonSimonLiebPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostSingletonSimonLiebLocalizationPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  refine ⟨hn H hH, ?_⟩
  intro v hv
  exact finiteBoundaryGhostLocalizedExpectation_boundary_le_boxExpectation
    β H n (Finset.mem_filter.mp hv).2


theorem finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLiebComparison
    (h :
      FiniteQ2SimonBoundaryGhostSingletonSimonLiebComparisonPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  exact
    finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb
      (hn H hH).1
      (hn H hH).2


theorem finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLieb
    (h :
      FiniteQ2SimonBoundaryGhostSingletonSimonLiebPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  exact
    finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLieb'
      (le_of_lt hβpos)
      hH
      (hn H hH)


theorem finiteQ2SimonBoundaryGhostComparison_of_scalarBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLieb
    (finiteQ2SimonBoundaryGhostSingletonSimonLieb_of_scalarBound h)


theorem finiteQ2SimonBoundaryGhostComparison_of_scalarCurrentBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarCurrentBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_scalarBound
    (finiteQ2SimonBoundaryGhostScalarBound_of_scalarCurrentBound h)


theorem finiteQ2SimonBoundaryGhostComparison_of_scalarCurrentSumBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarCurrentSumBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_scalarBound
    (finiteQ2SimonBoundaryGhostScalarBound_of_scalarCurrentSumBound h)


theorem finiteQ2SimonBoundaryGhostComparison_of_sourcePairBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarSourcePairBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_scalarCurrentSumBound
    (finiteQ2SimonBoundaryGhostScalarCurrentSumBound_of_sourcePairBound h)


theorem finiteQ2SimonBoundaryGhostComparison_of_edgeCopyBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarEdgeCopyBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_sourcePairBound
    (finiteQ2SimonBoundaryGhostScalarSourcePairBound_of_edgeCopyBound h)


theorem finiteQ2SimonBoundaryGhostComparison_of_emptyCollapsedBound
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBoundPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_edgeCopyBound
    (finiteQ2SimonBoundaryGhostScalarEdgeCopyBound_of_emptyCollapsedBound h)


theorem finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_emptyCollapsedBound
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyBound_of_firstExitPositive h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_decrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_decrementedSourceAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryVertexDecrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexDecrementedSourceAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryVertexSigmaFiniteSubcaseAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexSigmaFiniteSubcaseAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryVertexSigmaFiniteLabelCaseAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexSigmaFiniteLabelCaseAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryVertexSigmaFiniteLabelCaseAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_globalDecrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_globalDecrementedSourceAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_sigmaDecrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_sigmaDecrementedSourceAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_sigmaFiniteSubcaseAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_sigmaFiniteSubcaseAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryMultiplicityAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryMultiplicityAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryMultiplicityAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberSourcePairProfileAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairProfileAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourcePairProfileAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberImageCardSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberImageCardSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
      (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberImageCardSourcePairAbsorption
        h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberDecomposedSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecomposedSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberDecomposedSourcePairAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairCurrentSumAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairCurrentSumAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberTanhNormalizedImageCardSourcePairComponentShareAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_tanhNormalizedBoundaryFiberImageCardSourcePairComponentShareAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberSourcePairAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
      (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourcePairAbsorption
        h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberCardCapAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCardCapAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberCardCapAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberUniformCardCapAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCardCapAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberUniformCardCapAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberUniformCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberUniformCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberUniformCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberCrossingPairCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberCrossingPairCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberDecrementImageMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem
    finiteQ2SimonBoundaryGhostComparison_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_boundaryFiberSourceSectorMultiplicityCapCappedComponentBudgetAbsorption
      h)


theorem finiteQ2SimonBoundaryGhostComparison_of_singletonSimonLiebLocalization
    (h :
      FiniteQ2SimonBoundaryGhostSingletonSimonLiebLocalizationPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  exact
    finiteBoundaryGhostCurrentOnePoint_le_currentBoundaryTwoPointSum_of_singletonSimonLiebLocalization
      (le_of_lt hβpos)
      hH
      (hn H hH).1
      (hn H hH).2


theorem le_of_forall_pos_le_add_real {a b : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → a ≤ b + ε) : a ≤ b := by
  by_contra hle
  have hlt : b < a := lt_of_not_ge hle
  have hε : 0 < (a - b) / 2 := by linarith
  have hmain := h ((a - b) / 2) hε
  linarith


theorem finiteCurrentSimon_pointwise_of_boundaryGhostApprox_comparison
    {β : ℝ} {n : ℕ}
    (happrox :
      ∀ ε : ℝ, 0 < ε →
        ∃ H : ℝ, 0 ≤ H ∧
          IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
              (IsingFK.boxOrigin 3 n)
            ≤ finiteBoundaryGhostCurrentOnePoint 3 n β H + ε)
    (hcompare :
      ∀ H : ℝ, 0 ≤ H →
        finiteBoundaryGhostCurrentOnePoint 3 n β H ≤
          finiteCurrentBoundaryTwoPointSum β n) :
    IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
        (IsingFK.boxOrigin 3 n)
      ≤ finiteCurrentBoundaryTwoPointSum β n := by
  refine le_of_forall_pos_le_add_real ?_
  intro ε hε
  obtain ⟨H, hH, hle⟩ := happrox ε hε
  calc
    IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
        (IsingFK.boxOrigin 3 n)
        ≤ finiteBoundaryGhostCurrentOnePoint 3 n β H + ε := hle
    _ ≤ finiteCurrentBoundaryTwoPointSum β n + ε :=
        by simpa [add_comm] using add_le_add_right (hcompare H hH) ε


theorem finiteCurrentSimon_of_boundaryGhostApprox_comparison
    (happrox :
      FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [happrox β hβpos hβc, hcompare β hβpos hβc] with
    n happrox_n hcompare_n
  exact finiteCurrentSimon_pointwise_of_boundaryGhostApprox_comparison
    happrox_n hcompare_n


theorem finiteCurrentSimon_of_boundaryGhostApprox_firstExitPositive
    (happrox :
      FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical :=
  finiteCurrentSimon_of_boundaryGhostApprox_comparison happrox
    (finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive hfirst)


theorem finiteExpectationJSimon_of_currentSimon
    (hSimon :
      FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryExpectationJPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hSimon β hβpos hβc] with n hSimon_n
  calc
    IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
        (IsingFK.boxOrigin 3 n)
        ≤
      finiteCurrentBoundaryTwoPointSum β n :=
          hSimon_n
    _ =
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
          (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v}) := by
          exact finiteCurrentBoundaryTwoPointSum_eq_expectationJBoundarySum
            β n


theorem finiteIsingTwoPoint_boxGraph_eq_expectationJ_symmDiff
    (d n : ℕ) (β : ℝ) (x y : FK.boxVerts d n) :
    (∑ σ : ConfigSpace (FK.boxVerts d n),
        Ising.isingProb (FK.boxGraph d n) β 0 σ *
          (Ising.spin σ x * Ising.spin σ y))
      =
    Sharpness.expectationJ (FK.boxGraph d n) β (fun _ => 1)
      (({x} : Finset (FK.boxVerts d n)) ∆ {y}) := by
  classical
  rw [Sharpness.expectationJ_one_eq_isingExpectation]
  unfold Ising.isingExpectation
  refine Finset.sum_congr rfl ?_
  intro σ _hσ
  congr 1
  have hx :
      Ising.spinProd ({x} : Finset (FK.boxVerts d n)) σ =
        Ising.spin σ x := by
    unfold Ising.spinProd
    simp
  have hy :
      Ising.spinProd ({y} : Finset (FK.boxVerts d n)) σ =
        Ising.spin σ y := by
    unfold Ising.spinProd
    simp
  calc
    Ising.spin σ x * Ising.spin σ y =
        Ising.spinProd ({x} : Finset (FK.boxVerts d n)) σ *
          Ising.spinProd ({y} : Finset (FK.boxVerts d n)) σ := by
          rw [hx, hy]
    _ =
        Ising.spinProd (({x} : Finset (FK.boxVerts d n)) ∆ {y}) σ :=
          Ising.spinProd_mul_self
            ({x} : Finset (FK.boxVerts d n)) {y} σ


theorem finiteIsingBoundaryTwoPointSum_eq_expectationJBoundarySum
    {β : ℝ} (n : ℕ) :
    (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ∑ σ : ConfigSpace (FK.boxVerts 3 n),
          Ising.isingProb (FK.boxGraph 3 n) β 0 σ *
            (Ising.spin σ (IsingFK.boxOrigin 3 n) * Ising.spin σ v))
      =
    ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
      Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
        (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v}) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro v _hv
  exact finiteIsingTwoPoint_boxGraph_eq_expectationJ_symmDiff
    3 n β (IsingFK.boxOrigin 3 n) v


theorem finiteIsingSimon_of_expectationJSimon
    (hSimon :
      FiniteQ2SimonFreeBoundaryExpectationJPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hSimon β hβpos hβc] with n hSimon_n
  calc
    IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
        (IsingFK.boxOrigin 3 n)
        ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        Sharpness.expectationJ (FK.boxGraph 3 n) β (fun _ => 1)
          (({IsingFK.boxOrigin 3 n} : Finset (FK.boxVerts 3 n)) ∆ {v}) :=
          hSimon_n
    _ =
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ∑ σ : ConfigSpace (FK.boxVerts 3 n),
          Ising.isingProb (FK.boxGraph 3 n) β 0 σ *
            (Ising.spin σ (IsingFK.boxOrigin 3 n) * Ising.spin σ v) := by
          exact (finiteIsingBoundaryTwoPointSum_eq_expectationJBoundarySum
            n).symm


theorem finiteIsingSimon_of_currentSimon
    (hSimon :
      FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical :=
  finiteIsingSimon_of_expectationJSimon
    (finiteExpectationJSimon_of_currentSimon hSimon)


theorem finiteIsingSimon_of_boundaryGhostApprox_comparison
    (happrox :
      FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical :=
  finiteIsingSimon_of_currentSimon
    (finiteCurrentSimon_of_boundaryGhostApprox_comparison happrox hcompare)


theorem finiteIsingSimon_of_boundaryGhostApprox_firstExitPositive
    (happrox :
      FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical :=
  finiteIsingSimon_of_boundaryGhostApprox_comparison happrox
    (finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive hfirst)


theorem finiteIsingBoundaryTwoPointSum_eq_freeFKBoundaryConnSum
    {β : ℝ} (hβpos : 0 < β) (n : ℕ) :
    (∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ∑ σ : ConfigSpace (FK.boxVerts 3 n),
          Ising.isingProb (FK.boxGraph 3 n) β 0 σ *
            (Ising.spin σ (IsingFK.boxOrigin 3 n) * Ising.spin σ v))
      =
    ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
      ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) := by
  classical
  refine Finset.sum_congr rfl ?_
  intro v _hv
  exact finiteIsingTwoPoint_boxGraph_eq_freeFiniteMeasure_boxConnEvent_of_beta_pos
    3 n hβpos (IsingFK.boxOrigin 3 n) v


theorem finiteQ2_wiredOnePoint_eq_wiredFKBoundaryConn
    {β : ℝ} (hβpos : 0 < β) {n : ℕ} (hn : 1 ≤ n) :
    IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
        (IsingFK.boxOrigin 3 n)
      =
    ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxBdryConnEvent 3 n) := by
  classical
  obtain ⟨v₀, hv₀⟩ :=
    IsingFK.boxBoundary_nonempty 3 n (by norm_num : 1 ≤ 3) hn
  calc
    IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
        (IsingFK.boxOrigin 3 n)
        =
      IsingFK.esWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n)
        (0 : Fin 2) (IsingFK.pOfBeta β) (IsingFK.boxOrigin 3 n) := by
          exact (IsingFK.esWiredOnePoint_pOfBeta_eq_isingWiredOnePoint
            (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
            (IsingFK.boxOrigin 3 n)).symm
    _ =
      IsingFK.wiredConnToBdryProb (FK.boxGraph 3 n) (FK.boxBoundary 3 n)
        (IsingFK.pOfBeta β) (IsingFK.boxOrigin 3 n) := by
          exact IsingFK.esWiredOnePoint_eq_wiredConnToBdryProb
            (FK.boxGraph 3 n) (FK.boxBoundary 3 n) (IsingFK.pOfBeta β)
            (IsingFK.boxOrigin 3 n) v₀ hv₀
    _ =
      ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
          (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
        : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
          (FK.boxBdryConnEvent 3 n) := by
            exact (FK.wiredFiniteMeasure_real_boxBdryConnEvent
              3 n (Ising.pOfBeta_pos hβpos) (Ising.pOfBeta_lt_one β)).symm


theorem freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon
    (hSimon :
      FiniteQ2SimonFreeBoundaryIsingBoxPositiveSubcritical) :
    FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hSimon β hβpos hβc, eventually_ge_atTop 1] with n hSimon_n hn
  calc
    ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxBdryConnEvent 3 n)
        =
      IsingFK.isingWiredOnePoint (FK.boxGraph 3 n) (FK.boxBoundary 3 n) β
        (IsingFK.boxOrigin 3 n) := by
          exact (finiteQ2_wiredOnePoint_eq_wiredFKBoundaryConn
            hβpos hn).symm
    _ ≤
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ∑ σ : ConfigSpace (FK.boxVerts 3 n),
          Ising.isingProb (FK.boxGraph 3 n) β 0 σ *
            (Ising.spin σ (IsingFK.boxOrigin 3 n) * Ising.spin σ v) :=
          hSimon_n
    _ =
      ∑ v ∈ Finset.univ.filter (FK.boxBoundary 3 n),
        ((FK.freeFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
            (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
          : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
            (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v) := by
          exact finiteIsingBoundaryTwoPointSum_eq_freeFKBoundaryConnSum hβpos n


theorem freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_currentSimon
    (hSimon :
      FiniteQ2SimonFreeBoundaryCurrentPositiveSubcritical) :
    FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_finiteIsingSimon
    (finiteIsingSimon_of_currentSimon hSimon)


theorem freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_boundaryGhostApprox_comparison
    (happrox :
      FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
    (hcompare :
      FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical) :
    FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_currentSimon
    (finiteCurrentSimon_of_boundaryGhostApprox_comparison happrox hcompare)


theorem freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_boundaryGhostApprox_firstExitPositive
    (happrox :
      FiniteQ2SimonBoundaryGhostApproxPositiveSubcritical)
    (hfirst :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical) :
    FreeQ2BoundaryProfileFiniteFKSimonFreeSumPositiveSubcritical :=
  freeQ2BoundaryProfileFiniteFKSimonFreeSum_of_boundaryGhostApprox_comparison
    happrox
    (finiteQ2SimonBoundaryGhostComparison_of_firstExitPositive hfirst)


end Exact3D
end StatMech
