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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part83
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorption_of_sigmaFiniteSubcaseAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  let f := finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n
  have hf_nonneg : 0 ≤ f := by
    intro a
    exact
      finiteBoundaryGhostDecrementedSourceWeightSigmaSummand_nonneg
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) a
  have hfinite :
      ∀ Ω : Finset (Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n)),
        (∑ a ∈ Ω, f a) ≤
          finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n :=
    hn H hH
  exact
    ⟨summable_of_sum_le hf_nonneg hfinite,
      Real.tsum_le_of_sum_le hf_nonneg hfinite⟩


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorption_of_finiteDecrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaFiniteSubcaseAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  exact
    (finiteBoundaryGhostDecrementedSourceWeightSigmaSubcase_sum_le_cutoffSum
      (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ω).trans
      (hn H hH (Ω.image Sigma.fst))


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorption_of_sigmaDecrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopySigmaDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH
  rcases hn H hH with ⟨hsigma, hbound⟩
  have hsumFiber :
      Summable (fun m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
        ∑' a : finiteBoundaryGhostDecrementedSourceWeightFiber n m,
          finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n ⟨m, a⟩) :=
    hsigma.sigma
  have hsumCurrent :
      Summable (finiteBoundaryGhostDecrementedSourceWeightSummand β H n) := by
    refine hsumFiber.congr ?_
    intro m
    exact
      (finiteBoundaryGhostDecrementedSourceWeightSummand_eq_tsum_fiber
        β H n m).symm
  refine ⟨hsumCurrent, ?_⟩
  calc
    (∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ,
        finiteBoundaryGhostDecrementedSourceWeightSummand β H n m)
        =
      ∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ,
        ∑' a : finiteBoundaryGhostDecrementedSourceWeightFiber n m,
          finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n ⟨m, a⟩ := by
      refine tsum_congr ?_
      intro m
      exact finiteBoundaryGhostDecrementedSourceWeightSummand_eq_tsum_fiber
        β H n m
    _ =
      ∑' a : Sigma (finiteBoundaryGhostDecrementedSourceWeightFiber n),
        finiteBoundaryGhostDecrementedSourceWeightSigmaSummand β H n a := by
      exact (Summable.tsum_sigma hsigma).symm
    _ ≤ finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n :=
      hbound


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_globalDecrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyGlobalDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  rcases hn H hH with ⟨hsum, hbound⟩
  calc
    finiteBoundaryGhostDecrementedSourceWeightCutoffSum β H n Ω =
        ∑ m ∈ Ω,
          finiteBoundaryGhostDecrementedSourceWeightSummand β H n m :=
      finiteBoundaryGhostDecrementedSourceWeightCutoffSum_eq_finset_sum_summand
        β H n Ω
    _ ≤
        ∑' m : ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ,
          finiteBoundaryGhostDecrementedSourceWeightSummand β H n m :=
      hsum.sum_le_tsum Ω
        (fun m _hm =>
          finiteBoundaryGhostDecrementedSourceWeightSummand_nonneg
            (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) m)
    _ ≤ finiteBoundaryGhostSimonCollapsedDenominatorProduct β H n :=
      hbound


theorem
    finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_decrementedSourceAbsorption
    (h :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω
  exact
    le_trans
      (finiteBoundaryGhostCollapsedSourceSummand_finset_sum_le_decrementedSourceWeightCutoffSum
        (β := β) (H := H) (le_of_lt hβpos) (le_of_lt hH) Ω)
      (hn H hH Ω)


end Exact3D
end StatMech
