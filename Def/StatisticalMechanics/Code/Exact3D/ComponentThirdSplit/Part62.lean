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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part59
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipResidualShellShare15.FieldwiseLeMul
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
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v false false false k ≤ Sh.four_none k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false true →
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v false false true k ≤ Sh.four_endpoint k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true false →
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v false true false k ≤ Sh.four_origin k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true true →
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v false true true k ≤ Sh.four_origin_endpoint k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false false →
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v true false false k ≤ Sh.four_ghost k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false true →
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v true false true k ≤ Sh.four_ghost_endpoint k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true false →
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v true true false k ≤ Sh.four_ghost_origin k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true true →
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualExactCardImageSourceClassSum
        β H n Ω v true true true k ≤
          Sh.four_ghost_origin_endpoint k * D)

set_option linter.style.longLine false in


def SourceClassEndpointMembershipResidualShellShare15.SupportFieldwiseLeMul
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
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v false false false k ≤ Sh.four_none k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false false true →
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v false false true k ≤ Sh.four_endpoint k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true false →
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v false true false k ≤ Sh.four_origin k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v false true true →
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v false true true k ≤
          Sh.four_origin_endpoint k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false false →
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v true false false k ≤ Sh.four_ghost k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true false true →
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v true false true k ≤ Sh.four_ghost_endpoint k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true false →
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v true true false k ≤ Sh.four_ghost_origin k * D) ∧
    (∀ k, k ∈
      finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
        v true true true →
      finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
        β H n Ω v true true true k ≤
          Sh.four_ghost_origin_endpoint k * D)

end Exact3D
end StatMech
