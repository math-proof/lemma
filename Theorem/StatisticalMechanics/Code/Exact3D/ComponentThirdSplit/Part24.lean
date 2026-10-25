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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part24
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorizationWithInactiveClassifiedCoefficientWeightNonzero_of_sourceActiveProfile
    (hactive :
      BoundaryVertexDecrementedSourceSourceActiveSigmaProfileWeightNonzeroBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationWithInactiveClassifiedCoefficientWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hactive β hβpos hβc] with n hnactive
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have hactivev :
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
          β H n Ωnz v ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n Ωnz v := by
    simpa [
      Ωnz,
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution]
      using hnactive H hH Ω v hv
  have hinactivev :
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
          β H n Ωnz v ≤
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum
          β H n Ωnz v :=
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder_le_sourceInactiveClassifiedCoefficientWeightSum
      (n := n) (β := β) (H := H)
      (le_of_lt hβpos) (le_of_lt hH) Ωnz v
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ωnz v =
        finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v +
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceInactiveRemainder
            β H n Ωnz v :=
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_sourceSplit
        β H n Ωnz v
    _ ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
            β H n Ωnz v +
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum
            β H n Ωnz v :=
      add_le_add hactivev hinactivev

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorizationWithInactiveClassifiedCoefficientWeightNonzero :
    BoundaryVertexDecrementedSourceProfileMajorizationWithInactiveClassifiedCoefficientWeightNonzeroPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorizationWithInactiveClassifiedCoefficientWeightNonzero_of_sourceActiveProfile
    sourceActiveSigmaProfileWeightNonzeroBranch

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficientWeightNonzero_of_inactiveClassifiedCoefficient
    (hcoeff :
      BoundaryVertexDecrementedSourceProfileMajorizationWithInactiveClassifiedCoefficientWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficientWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hcoeff β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have htarget :
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum
          β H n Ωnz v ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
            β H n Ωnz v +
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum
            β H n Ωnz v := by
    simpa [Ωnz] using hn H hH Ω v hv
  rw [
    finiteBoundaryGhostSourceInactiveClassifiedCoefficientWeightSum_eq_nonTwoPointClassFilter
      β H n Ωnz v] at htarget
  simpa [
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfileWithNonTwoPointClassifiedCoefficient]
    using htarget

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficientWeightNonzero :
    BoundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficientWeightNonzeroPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficientWeightNonzero_of_inactiveClassifiedCoefficient
    boundaryVertexDecrementedSourceProfileMajorizationWithInactiveClassifiedCoefficientWeightNonzero

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficient_of_weightNonzero
    (h :
      BoundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficientWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficientPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  have hvbdry : FK.boxBoundary 3 n v :=
    (Finset.mem_filter.mp hv).2
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ω v =
        finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
          (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v :=
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_eq_weightNonzeroCutoff
        β H n Ω hvbdry
    _ ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfileWithNonTwoPointClassifiedCoefficient
          β H n (finiteBoundaryGhostWeightNonzeroCutoff β H n Ω) v :=
      hn H hH Ω v hv

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficient :
    BoundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficientPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficient_of_weightNonzero
    boundaryVertexDecrementedSourceProfileMajorizationWithNonTwoPointClassifiedCoefficientWeightNonzero

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorizationWeightNonzero_of_sourceActiveProfile_inactiveZero
    (hactive :
      BoundaryVertexDecrementedSourceSourceActiveSigmaProfileWeightNonzeroBranchPositiveSubcritical)
    (hinactive :
      BoundaryVertexDecrementedSourceSourceInactiveSigmaZeroWeightNonzeroBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hactive β hβpos hβc, hinactive β hβpos hβc] with
    n hnactive hninactive
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let S :=
    finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport
      n Ωnz v
  let P :
      Sigma (fun m :
        ↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ =>
        finiteBoundaryGhostDecrementedSourceWeightVertexFiber n m v) → Prop :=
    fun a => finiteBoundaryGhostFullSourceOnePoint n a.1
  have hactivev :
      (∑ a ∈ S.filter P,
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a) ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n Ωnz v := by
    simpa [S, P, Ωnz] using hnactive H hH Ω v hv
  have hinactivev :
      (∑ a ∈ S.filter (fun a => ¬ P a),
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a) ≤ 0 := by
    simpa [S, P, Ωnz] using hninactive H hH Ω v hv
  have hS :
      (∑ a ∈ S,
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a) ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
          β H n Ωnz v := by
    refine
      finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSubcase_sum_le_of_filter_le_filter_not_le
        β H S P hactivev hinactivev ?_
    exact le_of_eq (by ring)
  calc
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n Ωnz v =
        ∑ a ∈ S,
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSummand
            β H n v a :=
      (finiteBoundaryGhostDecrementedSourceWeightVertexSigmaCurrentSupport_sum_eq_vertexCutoffSum
        β H n Ωnz v).symm
    _ ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v :=
      hS

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_sourceActiveProfile_inactiveZero
    (hactive :
      BoundaryVertexDecrementedSourceSourceActiveSigmaProfileWeightNonzeroBranchPositiveSubcritical)
    (hinactive :
      BoundaryVertexDecrementedSourceSourceInactiveSigmaZeroWeightNonzeroBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorization_of_weightNonzero
    (boundaryVertexDecrementedSourceProfileMajorizationWeightNonzero_of_sourceActiveProfile_inactiveZero
      hactive hinactive)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_ghostEdgeMultiplicitySplit
    (hlow :
      BoundaryVertexDecrementedSourceLowGhostMultiplicityEmptyBranchPositiveSubcritical)
    (hres :
      BoundaryVertexDecrementedSourceResidualGhostMultiplicityMainBranchPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hlow β hβpos hβc, hres β hβpos hβc] with
    n hnlow hnres
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let e := finiteBoundaryGhostBoundaryEdge n v
  have hlowv :
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
          (Ω.filter (fun m => m e ≤ (1 : ℕ))) v ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexEmptyTerm β H n v := by
    simpa [e] using hnlow H hH Ω v hv
  have hresv :
      finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum β H n
          (Ω.filter (fun m => ¬ m e ≤ (1 : ℕ))) v ≤
        finiteBoundaryGhostCollapsedCutoffBoundaryFiberCard n Ωnz v *
          finiteBoundaryGhostBoundaryFiberSourcePairVertexMainTerm β H n v := by
    simpa [Ωnz, e] using hnres H hH Ω v hv
  refine
    finiteBoundaryGhostDecrementedSourceWeightVertexCutoffSum_le_boundaryFiberSourcePairVertexProfile_weightNonzeroCutoff_of_filter_le_filter_not_le
      β H n Ω v (fun m => m e ≤ (1 : ℕ))
      hlowv hresv ?_
  rw [
    finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile_eq_card_mul_main_add_empty]
  exact le_of_eq (by ring)

set_option linter.style.longLine false in


theorem
    boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsource :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryVertexDecrementedSourceAbsorptionPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hmajor β hβpos hβc, hsource β hβpos hβc] with
    n hnmajor hnsource
  intro H hH Ω v hv
  exact (hnmajor H hH Ω v hv).trans (hnsource H hH Ω v hv)

set_option linter.style.longLine false in


theorem finiteCutoffBound_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsource :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBoundPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteCutoffBound_of_decrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption
      (boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourcePairAbsorption
        hmajor hsource))

set_option linter.style.longLine false in


theorem firstExitPositive_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsource :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFirstExitPositive_of_decrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption
      (boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourcePairAbsorption
        hmajor hsource))

set_option linter.style.longLine false in


theorem boundaryGhostComparison_of_decrementedSourceProfileMajorization_sourcePairAbsorption
    (hmajor :
      BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical)
    (hsource :
      FiniteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteBoundaryFiberWeightNonzeroCutoffSourcePairAbsorptionPositiveSubcritical) :
    FiniteQ2SimonBoundaryGhostComparisonPositiveSubcritical :=
  finiteQ2SimonBoundaryGhostComparison_of_decrementedSourceAbsorption
    (finiteQ2SimonBoundaryGhostScalarCollapsedEdgeCopyFiniteDecrementedSourceAbsorption_of_boundaryVertexDecrementedSourceAbsorption
      (boundaryVertexDecrementedSourceAbsorption_of_decrementedSourceProfileMajorization_sourcePairAbsorption
        hmajor hsource))

end Exact3D
end StatMech
