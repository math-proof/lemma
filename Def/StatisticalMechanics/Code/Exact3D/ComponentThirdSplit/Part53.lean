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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part50
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def SourceClassEndpointMembershipResidualShellShare15.residualEnvelopeClassifiedCardFourMajorant
    {n : ℕ} (v : FK.boxVerts 3 n)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (residualEnvelope :
      Bool → Bool → Bool → Finset (Option (FK.boxVerts 3 n)) → ℝ) :
    Bool → Bool → Bool → ℕ → ℝ :=
  fun hasGhost hasOrigin hasEndpoint k =>
    ∑ R ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k,
      ((finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R).card : ℝ) *
        residualEnvelope hasGhost hasOrigin hasEndpoint R

set_option linter.style.longLine false in


noncomputable def SourceClassEndpointMembershipResidualShellShare15.pointwiseClassifiedFourMajorant
    {n : ℕ} (v : FK.boxVerts 3 n)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (pointMajorant :
      ∀ (_ : Bool) (_ : Bool) (_ : Bool)
        (_ : Finset (Option (FK.boxVerts 3 n))),
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ℝ) :
    Bool → Bool → Bool → ℕ → ℝ :=
  fun hasGhost hasOrigin hasEndpoint k =>
    ∑ R ∈
      finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k,
      ∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
          v Ω hasGhost hasOrigin hasEndpoint R,
        pointMajorant hasGhost hasOrigin hasEndpoint R E

end Exact3D
end StatMech
