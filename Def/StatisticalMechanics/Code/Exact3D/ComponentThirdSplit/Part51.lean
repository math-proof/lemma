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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part48
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
    {n : ℕ} (v : FK.boxVerts 3 n)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*)
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    (label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R)
    (hasGhost hasOrigin hasEndpoint : Bool) (k : ℕ) : ℝ :=
  ∑ R ∈
    finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet v k,
    ∑ i : ι hasGhost hasOrigin hasEndpoint R,
      ∑ E ∈
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
          v Ω hasGhost hasOrigin hasEndpoint R
          (label hasGhost hasOrigin hasEndpoint R) i,
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E

end Exact3D
end StatMech
