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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part74
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    0 ≤
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
        β H n Ω v := by
  classical
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v
  have hB :
      SourceClassEndpointMembershipLiveBudget15.Nonneg B := by
    simpa [B] using
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15_nonneg
        hβ hH n Ω v
  rcases hB with
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, _hfourNoneBudget,
      _hfourEndpointBudget, _hfourOriginBudget,
      _hfourOriginEndpointBudget, _hfourGhostBudget,
      _hfourGhostEndpointBudget, _hfourGhostOriginBudget,
      _hfourGhostOriginEndpointBudget⟩
  have hfourNone :
      0 ≤
        ∑ k ∈ Finset.Icc 4 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v false false false k :=
    Finset.sum_nonneg fun k _hk =>
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_nonneg
        hβ hH n Ω v false false false k
  have hfourEndpoint :
      0 ≤
        ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v false false true k :=
    Finset.sum_nonneg fun k _hk =>
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_nonneg
        hβ hH n Ω v false false true k
  have hfourOrigin :
      0 ≤
        ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v false true false k :=
    Finset.sum_nonneg fun k _hk =>
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_nonneg
        hβ hH n Ω v false true false k
  have hfourOriginEndpoint :
      0 ≤
        ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v false true true k :=
    Finset.sum_nonneg fun k _hk =>
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_nonneg
        hβ hH n Ω v false true true k
  have hfourGhost :
      0 ≤
        ∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v true false false k :=
    Finset.sum_nonneg fun k _hk =>
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_nonneg
        hβ hH n Ω v true false false k
  have hfourGhostEndpoint :
      0 ≤
        ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v true false true k :=
    Finset.sum_nonneg fun k _hk =>
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_nonneg
        hβ hH n Ω v true false true k
  have hfourGhostOrigin :
      0 ≤
        ∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v true true false k :=
    Finset.sum_nonneg fun k _hk =>
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum_nonneg
        hβ hH n Ω v true true false k
  dsimp [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal,
    B]
  linarith

end Exact3D
end StatMech
