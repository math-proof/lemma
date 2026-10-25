/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part22
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackSourceClassSupportBudget_of_sourceClassSupportShare
    (hshare :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackSourceClassSupportShareWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackSourceClassSupportBudgetWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hshare β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  let slack :=
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ωnz v
  rcases hn H hH Ω v hv with
    ⟨hslackNonneg, coefficientShare, _hshareNonneg, hshareTotal, hcase⟩
  have hslackNonneg' : 0 ≤ slack := by
    simpa [slack, Ωnz] using hslackNonneg
  have hshareTotal' :
      (∑ S ∈ sourceClassSupport, coefficientShare S) ≤ 1 := by
    simpa [sourceClassSupport, Ωnz] using hshareTotal
  refine ⟨fun S => coefficientShare S * slack, ?_, ?_⟩
  · intro S hS
    simpa [sourceClassSupport, slack, Ωnz] using hcase S hS
  · calc
      (∑ S ∈ sourceClassSupport, coefficientShare S * slack) =
          (∑ S ∈ sourceClassSupport, coefficientShare S) * slack := by
        rw [← Finset.sum_mul]
      _ ≤ 1 * slack :=
        mul_le_mul_of_nonneg_right hshareTotal' hslackNonneg'
      _ = slack := by
        ring

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_sourceClassSupportShare
    (hshare :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackSourceClassSupportShareWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_sourceClassSupportBudget
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackSourceClassSupportBudget_of_sourceClassSupportShare
      hshare)

set_option linter.style.longLine false in


theorem activePlusInactiveClassifiedCoefficient_of_activePlusNonTwoPointClassifiedCoefficient
    (hnon :
      BoundaryVertexDecrementedSourceProfileMajorizationActivePlusNonTwoPointClassifiedCoefficientWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationActivePlusInactiveClassifiedCoefficientWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hnon β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have htarget :
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
          β H n Ωnz v +
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n Ωnz v := by
    simpa [Ωnz] using hn H hH Ω v hv
  rw [← finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum_eq_nonTwoPointClassFilter
    β H n Ωnz v] at htarget
  exact htarget

set_option linter.style.longLine false in
set_option maxHeartbeats 1200000 in


theorem boundaryVertexDecrementedSourceProfileMajorizationWeightNonzero_of_activePlusInactiveClassifiedCoefficient
    (hcoeff :
      BoundaryVertexDecrementedSourceProfileMajorizationActivePlusInactiveClassifiedCoefficientWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcoeff β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have hinactive :
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
          β H n Ωnz v ≤
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum
          β H n Ωnz v := by
    exact
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder_le_sourceInactiveClassifiedCoefficientWeightSum
        (n := n) (β := β) (H := H)
        (le_of_lt hβpos) (le_of_lt hH) Ωnz v
  have htarget :
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
          β H n Ωnz v +
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum
          β H n Ωnz v ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n Ωnz v := by
    simpa [Ωnz] using hn H hH Ω v hv
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ωnz v =
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v +
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
            β H n Ωnz v :=
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_sourceSplit
        β H n Ωnz v
    _ ≤
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v +
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum
            β H n Ωnz v :=
      add_le_add
        (le_refl
          (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v))
        hinactive
    _ ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n Ωnz v :=
      htarget

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_activePlusInactiveClassifiedCoefficient
    (hcoeff :
      BoundaryVertexDecrementedSourceProfileMajorizationActivePlusInactiveClassifiedCoefficientWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorization_of_weightNonzero
    (boundaryVertexDecrementedSourceProfileMajorizationWeightNonzero_of_activePlusInactiveClassifiedCoefficient
      hcoeff)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorizationWeightNonzero_of_activePlusNonTwoPointClassifiedCoefficient
    (hnon :
      BoundaryVertexDecrementedSourceProfileMajorizationActivePlusNonTwoPointClassifiedCoefficientWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationWeightNonzeroPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorizationWeightNonzero_of_activePlusInactiveClassifiedCoefficient
    (activePlusInactiveClassifiedCoefficient_of_activePlusNonTwoPointClassifiedCoefficient
      hnon)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_activePlusNonTwoPointClassifiedCoefficient
    (hnon :
      BoundaryVertexDecrementedSourceProfileMajorizationActivePlusNonTwoPointClassifiedCoefficientWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorization_of_weightNonzero
    (boundaryVertexDecrementedSourceProfileMajorizationWeightNonzero_of_activePlusNonTwoPointClassifiedCoefficient
      hnon)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
    (hslack :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorization_of_activePlusNonTwoPointClassifiedCoefficient
    (activePlusNonTwoPointClassifiedCoefficient_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
      hslack)

set_option linter.style.longLine false in


theorem sourceActiveSigmaProfileWeightNonzeroBranch_of_currentProfile
    (hcurrent :
      BoundaryVertexDecrementedSourceSourceActiveCurrentProfileWeightNonzeroBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceSourceActiveSigmaProfileWeightNonzeroBranchPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcurrent β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have hcurrentv :
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
          (Ωnz.filter
            (fun m => finiteBoundaryGhostFullSourceOnePoint n m)) v ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n Ωnz v := by
    simpa [Ωnz] using hn H hH Ω v hv
  have hsum :
      (∑ a ∈
          (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
            n Ωnz v).filter
            (fun a => finiteBoundaryGhostFullSourceOnePoint n a.1),
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a) =
        finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
          (Ωnz.filter
            (fun m => finiteBoundaryGhostFullSourceOnePoint n m)) v := by
    simpa [
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution]
      using
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution_eq_vertexCutoffSum_filter_fullSourceOnePoint
          β H n Ωnz v
  exact hsum.trans_le hcurrentv

set_option linter.style.longLine false in


theorem sourceActiveSigmaProfileWeightNonzeroBranch :
    BoundaryVertexDecrementedSourceSourceActiveSigmaProfileWeightNonzeroBranchPositiveSubcritical :=
  sourceActiveSigmaProfileWeightNonzeroBranch_of_currentProfile
    sourceActiveCurrentProfileWeightNonzeroBranch

set_option linter.style.longLine false in


theorem finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    0 ≤
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
        β H n Ω v := by
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
  exact
    Finset.sum_nonneg
      (fun a _ha =>
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_nonneg
          (β := β) (H := H) hβ hH a)

set_option linter.style.longLine false in


theorem finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution_nonneg
    {β H : ℝ} {n : ℕ}
    (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    0 ≤
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
        β H n Ω v := by
  unfold finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
  exact
    Finset.sum_nonneg
      (fun a _ha =>
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand_nonneg
          (β := β) (H := H) hβ hH a)

end Exact3D
end StatMech
