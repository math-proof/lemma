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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part44
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι}
    {labelShare : ι → ℝ}
    (h :
      SourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare
        v β H Ω hasGhost hasOrigin hasEndpoint R label labelShare D) :
    SourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare
      v β H Ω hasGhost hasOrigin hasEndpoint R
      (∑ i : ι, labelShare i) D := by
  classical
  refine ⟨?_, ?_⟩
  · exact Finset.sum_nonneg (fun i _hi => h.1 i)
  · rw [
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_eq_label_sum
        β H n Ω v hasGhost hasOrigin hasEndpoint R label]
    calc
      (∑ i : ι,
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSum
          v β H Ω hasGhost hasOrigin hasEndpoint R label i) ≤
          ∑ i : ι, labelShare i * D := by
        exact Finset.sum_le_sum (fun i _hi => h.2 i)
      _ = (∑ i : ι, labelShare i) * D := by
        simpa using
          (Finset.sum_mul (Finset.univ : Finset ι) labelShare D).symm

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseSourceClassSum_le_labelShareBudget
    {β H D budget : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {R : Finset (Option (FK.boxVerts 3 n))}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {label :
      finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v → ι}
    {labelShare : ι → ℝ}
    (h :
      SourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare
        v β H Ω hasGhost hasOrigin hasEndpoint R label labelShare D)
    (hbudget : (∑ i : ι, labelShare i) * D ≤ budget) :
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ω v
        (finiteBoundaryGhostSourceClassEndpointMarkedSources
          v hasGhost hasOrigin hasEndpoint ∪ R) ≤
      budget := by
  exact
    le_trans
      (sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := hasGhost) (hasOrigin := hasOrigin)
        (hasEndpoint := hasEndpoint) (R := R)
        (label := label) (labelShare := labelShare) h).2
      hbudget

end Exact3D
end StatMech
