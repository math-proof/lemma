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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part62
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.supportFieldwiseLeMul_of_fields
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
    (hzeroNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).zero_none ≤ Sh.zero_none * D)
    (htwoNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_none ≤ Sh.two_none * D)
    (htwoEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_endpoint ≤ Sh.two_endpoint * D)
    (htwoOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_origin ≤ Sh.two_origin * D)
    (htwoGhost :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost ≤ Sh.two_ghost * D)
    (htwoGhostEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_endpoint ≤
          Sh.two_ghost_endpoint * D)
    (htwoGhostOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_origin ≤ Sh.two_ghost_origin * D)
    (hfourNone :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v false false false →
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
          β H n Ω v false false false k ≤ Sh.four_none k * D)
    (hfourEndpoint :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v false false true →
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
          β H n Ω v false false true k ≤ Sh.four_endpoint k * D)
    (hfourOrigin :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v false true false →
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
          β H n Ω v false true false k ≤ Sh.four_origin k * D)
    (hfourOriginEndpoint :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v false true true →
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
          β H n Ω v false true true k ≤ Sh.four_origin_endpoint k * D)
    (hfourGhost :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v true false false →
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
          β H n Ω v true false false k ≤ Sh.four_ghost k * D)
    (hfourGhostEndpoint :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v true false true →
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
          β H n Ω v true false true k ≤ Sh.four_ghost_endpoint k * D)
    (hfourGhostOrigin :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v true true false →
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
          β H n Ω v true true false k ≤ Sh.four_ghost_origin k * D)
    (hfourGhostOriginEndpoint :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v true true true →
        finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardSourceClassSum
          β H n Ω v true true true k ≤
            Sh.four_ghost_origin_endpoint k * D) :
    Sh.SupportFieldwiseLeMul β H Ω D :=
  ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
    htwoGhostEndpoint, htwoGhostOrigin, hfourNone, hfourEndpoint,
    hfourOrigin, hfourOriginEndpoint, hfourGhost, hfourGhostEndpoint,
    hfourGhostOrigin, hfourGhostOriginEndpoint⟩

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.supportFieldwiseLeMul_of_cellShares
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
    (hzeroNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).zero_none ≤ Sh.zero_none * D)
    (htwoNone :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_none ≤ Sh.two_none * D)
    (htwoEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_endpoint ≤ Sh.two_endpoint * D)
    (htwoOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_origin ≤ Sh.two_origin * D)
    (htwoGhost :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost ≤ Sh.two_ghost * D)
    (htwoGhostEndpoint :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_endpoint ≤
          Sh.two_ghost_endpoint * D)
    (htwoGhostOrigin :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).two_ghost_origin ≤ Sh.two_ghost_origin * D)
    (hfourNone :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v false false false →
        SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
          v β H Ω false false false k (Sh.four_none k) D)
    (hfourEndpoint :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v false false true →
        SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
          v β H Ω false false true k (Sh.four_endpoint k) D)
    (hfourOrigin :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v false true false →
        SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
          v β H Ω false true false k (Sh.four_origin k) D)
    (hfourOriginEndpoint :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v false true true →
        SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
          v β H Ω false true true k (Sh.four_origin_endpoint k) D)
    (hfourGhost :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v true false false →
        SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
          v β H Ω true false false k (Sh.four_ghost k) D)
    (hfourGhostEndpoint :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v true false true →
        SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
          v β H Ω true false true k (Sh.four_ghost_endpoint k) D)
    (hfourGhostOrigin :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v true true false →
        SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
          v β H Ω true true false k (Sh.four_ghost_origin k) D)
    (hfourGhostOriginEndpoint :
      ∀ k, k ∈
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
          v true true true →
        SourceClassEndpointMembershipSupportResidualExactCardShellCellShare
          v β H Ω true true true k
          (Sh.four_ghost_origin_endpoint k) D) :
    Sh.SupportFieldwiseLeMul β H Ω D :=
  SourceClassEndpointMembershipResidualShellShare15.supportFieldwiseLeMul_of_fields
    hzeroNone htwoNone htwoEndpoint htwoOrigin htwoGhost
    htwoGhostEndpoint htwoGhostOrigin
    (fun k hk => (hfourNone k hk).2)
    (fun k hk => (hfourEndpoint k hk).2)
    (fun k hk => (hfourOrigin k hk).2)
    (fun k hk => (hfourOriginEndpoint k hk).2)
    (fun k hk => (hfourGhost k hk).2)
    (fun k hk => (hfourGhostEndpoint k hk).2)
    (fun k hk => (hfourGhostOrigin k hk).2)
    (fun k hk => (hfourGhostOriginEndpoint k hk).2)

end Exact3D
end StatMech
