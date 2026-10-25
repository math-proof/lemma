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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part51
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_classifiedSetSum
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R}
    {k : ℕ} :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
        v β H Ω ι label hasGhost hasOrigin hasEndpoint k =
      ∑ R ∈
        finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
          v k,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseClassifiedSet
            v Ω hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E := by
  classical
  unfold SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare
  apply Finset.sum_congr rfl
  intro R _hR
  have hlabel :
      (∑ i : ι hasGhost hasOrigin hasEndpoint R,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω hasGhost hasOrigin hasEndpoint R
            (label hasGhost hasOrigin hasEndpoint R) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E) =
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
          β H n Ω v
          (finiteBoundaryGhostSourceClassEndpointMarkedSources
            v hasGhost hasOrigin hasEndpoint ∪ R) := by
    rw [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_label_sum
        β H n Ω v hasGhost hasOrigin hasEndpoint R
        (label hasGhost hasOrigin hasEndpoint R)]
    apply Finset.sum_congr rfl
    intro i _hi
    exact
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum_eq_sum_labelSet
        v β H Ω hasGhost hasOrigin hasEndpoint R
        (label hasGhost hasOrigin hasEndpoint R) i).symm
  exact
    hlabel.trans
      (finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_sum_classifiedSet
        β H n Ω v hasGhost hasOrigin hasEndpoint R)

end Exact3D
end StatMech
