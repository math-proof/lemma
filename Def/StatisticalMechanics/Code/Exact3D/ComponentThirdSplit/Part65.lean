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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part62
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


def SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelFieldwiseLeMul
    {n : ℕ} {v : FK.boxVerts 3 n}
    (Sh : SourceClassEndpointMembershipResidualShellShare15 v)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (D : ℝ)
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
          ι hasGhost hasOrigin hasEndpoint R) : Prop :=
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
      β H n Ω v).two_ghost_endpoint ≤
        Sh.two_ghost_endpoint * D ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_origin ≤ Sh.two_ghost_origin * D ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
      β H Ω D false false false Sh.four_none (ι false false false)
      (label false false false) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
      β H Ω D false false true Sh.four_endpoint
      (ι false false true) (label false false true) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
      β H Ω D false true false Sh.four_origin
      (ι false true false) (label false true false) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
      β H Ω D false true true Sh.four_origin_endpoint
      (ι false true true) (label false true true) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
      β H Ω D true false false Sh.four_ghost
      (ι true false false) (label true false false) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
      β H Ω D true false true Sh.four_ghost_endpoint
      (ι true false true) (label true false true) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
      β H Ω D true true false Sh.four_ghost_origin
      (ι true true false) (label true true false) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
      β H Ω D true true true Sh.four_ghost_origin_endpoint
      (ι true true true) (label true true true)

set_option linter.style.longLine false in


def SourceClassEndpointMembershipResidualShellShare15.SupportResidualCasePointwiseDependentLabelFieldwiseLeMul
    {n : ℕ} {v : FK.boxVerts 3 n}
    (Sh : SourceClassEndpointMembershipResidualShellShare15 v)
    (β H : ℝ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (D : ℝ)
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
          ι hasGhost hasOrigin hasEndpoint R) : Prop :=
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
      β H n Ω v).two_ghost_endpoint ≤
        Sh.two_ghost_endpoint * D ∧
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_origin ≤ Sh.two_ghost_origin * D ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCasePointwiseDependentLabelField
      β H Ω D false false false Sh.four_none (ι false false false)
      (label false false false) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCasePointwiseDependentLabelField
      β H Ω D false false true Sh.four_endpoint
      (ι false false true) (label false false true) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCasePointwiseDependentLabelField
      β H Ω D false true false Sh.four_origin
      (ι false true false) (label false true false) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCasePointwiseDependentLabelField
      β H Ω D false true true Sh.four_origin_endpoint
      (ι false true true) (label false true true) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCasePointwiseDependentLabelField
      β H Ω D true false false Sh.four_ghost
      (ι true false false) (label true false false) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCasePointwiseDependentLabelField
      β H Ω D true false true Sh.four_ghost_endpoint
      (ι true false true) (label true false true) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCasePointwiseDependentLabelField
      β H Ω D true true false Sh.four_ghost_origin
      (ι true true false) (label true true false) ∧
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCasePointwiseDependentLabelField
      β H Ω D true true true Sh.four_ghost_origin_endpoint
      (ι true true true) (label true true true)

end Exact3D
end StatMech
