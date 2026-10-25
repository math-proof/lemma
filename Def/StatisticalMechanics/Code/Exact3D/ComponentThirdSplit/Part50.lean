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
import Theorem.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part47
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


noncomputable def SourceClassEndpointMembershipResidualShellShare15.normalizedRows
    {n : ℕ} (v : FK.boxVerts 3 n)
    (β H D : ℝ)
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
          ι hasGhost hasOrigin hasEndpoint R) :
    SourceClassEndpointMembershipResidualShellShare15 v where
  zero_none :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).zero_none / D
  two_none :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_none / D
  two_endpoint :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_endpoint / D
  two_origin :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_origin / D
  two_ghost :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost / D
  two_ghost_endpoint :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_endpoint / D
  two_ghost_origin :=
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v).two_ghost_origin / D
  four_none := fun k =>
    ∑ R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k,
      ∑ i : ι false false false R,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω false false false R (label false false false R) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / D
  four_endpoint := fun k =>
    ∑ R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k,
      ∑ i : ι false false true R,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω false false true R (label false false true R) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / D
  four_origin := fun k =>
    ∑ R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k,
      ∑ i : ι false true false R,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω false true false R (label false true false R) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / D
  four_origin_endpoint := fun k =>
    ∑ R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k,
      ∑ i : ι false true true R,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω false true true R (label false true true R) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / D
  four_ghost := fun k =>
    ∑ R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k,
      ∑ i : ι true false false R,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω true false false R (label true false false R) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / D
  four_ghost_endpoint := fun k =>
    ∑ R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k,
      ∑ i : ι true false true R,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω true false true R (label true false true R) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / D
  four_ghost_origin := fun k =>
    ∑ R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k,
      ∑ i : ι true true false R,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω true true false R (label true true false R) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / D
  four_ghost_origin_endpoint := fun k =>
    ∑ R ∈ finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
        v k,
      ∑ i : ι true true true R,
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω true true true R (label true true true R) i,
          finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
            β H E / D

end Exact3D
end StatMech
