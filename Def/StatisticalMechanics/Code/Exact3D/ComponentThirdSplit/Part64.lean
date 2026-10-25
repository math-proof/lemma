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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part61
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
    {n : ℕ} {v : FK.boxVerts 3 n}
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (D : ℝ)
    (hasGhost hasOrigin hasEndpoint : Bool)
    (fieldShare : ℕ → ℝ)
    (ι : Finset (Option (FK.boxVerts 3 n)) → Type*)
    [∀ R, Fintype (ι R)] [∀ R, DecidableEq (ι R)]
    (label :
      ∀ R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι R) : Prop :=
  ∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint →
    ∃ labelShare : ∀ R, ι R → ℝ,
      fieldShare k =
          ∑ R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k,
            ∑ i : ι R, labelShare R i ∧
        ∀ R, R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
            SourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare
            v β H Ω hasGhost hasOrigin hasEndpoint R (label R)
            (labelShare R) D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipResidualShellShare15.SupportResidualCasePointwiseDependentLabelField
    {n : ℕ} {v : FK.boxVerts 3 n}
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (D : ℝ)
    (hasGhost hasOrigin hasEndpoint : Bool)
    (fieldShare : ℕ → ℝ)
    (ι : Finset (Option (FK.boxVerts 3 n)) → Type*)
    [∀ R, Fintype (ι R)] [∀ R, DecidableEq (ι R)]
    (label :
      ∀ R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι R) : Prop :=
  ∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v hasGhost hasOrigin hasEndpoint →
    ∃ atomShare :
        Finset (Option (FK.boxVerts 3 n)) →
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ℝ,
      fieldShare k =
          ∑ R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k,
            ∑ i : ι R,
              ∑ E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                  v Ω hasGhost hasOrigin hasEndpoint R (label R) i,
                atomShare R E ∧
        ∀ R, R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k →
          SourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare
            v β H Ω hasGhost hasOrigin hasEndpoint R (atomShare R) D

end Exact3D
end StatMech
