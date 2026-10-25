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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part75
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageCanonicalTotal_eq_remaining_add_ghostOriginEndpointContribution
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageCanonicalTotal
        β H n Ω v =
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ω v +
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointContribution
          β H n Ω v := by
  rfl

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageCanonicalTotal_lt_of_remaining_add_ghostOriginEndpointContribution_lt
    {β H bound : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    (h :
      finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageRemainingTotal
          β H n Ω v +
        finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageGhostOriginEndpointContribution
          β H n Ω v < bound) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageCanonicalTotal
        β H n Ω v < bound := by
  rw [
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageCanonicalTotal_eq_remaining_add_ghostOriginEndpointContribution]
  exact h

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageCanonicalTotal_eq
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    finiteBoundaryGhostSourceClassEndpointMembershipConcreteIccExactCardImageCanonicalTotal
        β H n Ω v =
      let B :=
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
          β H n Ω v
      B.zero_none +
        B.two_none +
        B.two_endpoint +
        B.two_origin +
        B.two_ghost +
        B.two_ghost_endpoint +
        B.two_ghost_origin +
        (∑ k ∈ Finset.Icc 4 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v false false false k) +
        (∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v false false true k) +
        (∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v false true false k) +
        (∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v false true true k) +
        (∑ k ∈ Finset.Icc 3 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v true false false k) +
        (∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v true false true k) +
        (∑ k ∈ Finset.Icc 2 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v true true false k) +
        (∑ k ∈ Finset.Icc 1 ((2 * n + 1) ^ 3 - 2),
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
            β H n Ω v true true true k) := by
  rfl

end Exact3D
end StatMech
