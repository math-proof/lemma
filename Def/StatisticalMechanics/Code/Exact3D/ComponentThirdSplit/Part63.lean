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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part60
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseFieldwiseLeMul
    {n : ℕ} {v : FK.boxVerts 3 n}
    (Sh : SourceClassEndpointMembershipResidualShellShare15 v)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (D : ℝ) : Prop :=
  (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).zero_none ≤ Sh.zero_none * D ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_none ≤ Sh.two_none * D ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_endpoint ≤ Sh.two_endpoint * D ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_origin ≤ Sh.two_origin * D ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost ≤ Sh.two_ghost * D ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_endpoint ≤ Sh.two_ghost_endpoint * D ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_origin ≤ Sh.two_ghost_origin * D ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false false →
      ∃ residualShare : Finset (Option (FK.boxVerts 3 n)) → ℝ,
        Sh.four_none k =
            ∑ R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k,
              residualShare R ∧
          ∀ R, R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k →
            SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
              v β H Ω false false false R (residualShare R) D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false true →
      ∃ residualShare : Finset (Option (FK.boxVerts 3 n)) → ℝ,
        Sh.four_endpoint k =
            ∑ R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k,
              residualShare R ∧
          ∀ R, R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k →
            SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
              v β H Ω false false true R (residualShare R) D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true false →
      ∃ residualShare : Finset (Option (FK.boxVerts 3 n)) → ℝ,
        Sh.four_origin k =
            ∑ R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k,
              residualShare R ∧
          ∀ R, R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k →
            SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
              v β H Ω false true false R (residualShare R) D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true true →
      ∃ residualShare : Finset (Option (FK.boxVerts 3 n)) → ℝ,
        Sh.four_origin_endpoint k =
            ∑ R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k,
              residualShare R ∧
          ∀ R, R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k →
            SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
              v β H Ω false true true R (residualShare R) D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false false →
      ∃ residualShare : Finset (Option (FK.boxVerts 3 n)) → ℝ,
        Sh.four_ghost k =
            ∑ R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k,
              residualShare R ∧
          ∀ R, R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k →
            SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
              v β H Ω true false false R (residualShare R) D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false true →
      ∃ residualShare : Finset (Option (FK.boxVerts 3 n)) → ℝ,
        Sh.four_ghost_endpoint k =
            ∑ R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k,
              residualShare R ∧
          ∀ R, R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k →
            SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
              v β H Ω true false true R (residualShare R) D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true false →
      ∃ residualShare : Finset (Option (FK.boxVerts 3 n)) → ℝ,
        Sh.four_ghost_origin k =
            ∑ R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k,
              residualShare R ∧
          ∀ R, R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k →
            SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
              v β H Ω true true false R (residualShare R) D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true true →
      ∃ residualShare : Finset (Option (FK.boxVerts 3 n)) → ℝ,
        Sh.four_ghost_origin_endpoint k =
            ∑ R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k,
              residualShare R ∧
          ∀ R, R ∈
              finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
                v k →
            SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
              v β H Ω true true true R (residualShare R) D)

set_option linter.style.longLine false in


def SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseLabelField
    {n : ℕ} {v : FK.boxVerts 3 n}
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (D : ℝ)
    (hasGhost hasOrigin hasEndpoint : Bool)
    (fieldShare : ℕ → ℝ)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (label :
      Finset (Option (FK.boxVerts 3 n)) →
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι) : Prop :=
  ∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint →
    ∃ labelShare : Finset (Option (FK.boxVerts 3 n)) → ι → ℝ,
      fieldShare k =
          ∑ R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k,
            ∑ i : ι, labelShare R i ∧
        ∀ R, R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          SourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare
            v β H Ω hasGhost hasOrigin hasEndpoint R (label R)
            (labelShare R) D

end Exact3D
end StatMech
