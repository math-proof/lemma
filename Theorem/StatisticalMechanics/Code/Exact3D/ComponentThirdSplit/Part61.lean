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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part63
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseFieldwiseLeMul_of_labelFields
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {Sh : SourceClassEndpointMembershipResidualShellShare15 v}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {labelNone labelEndpoint labelOrigin labelOriginEndpoint :
      Finset (Option (FK.boxVerts 3 n)) →
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι}
    {labelGhost labelGhostEndpoint labelGhostOrigin
        labelGhostOriginEndpoint :
      Finset (Option (FK.boxVerts 3 n)) →
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι}
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
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseLabelField
        β H Ω D false false false Sh.four_none labelNone)
    (hfourEndpoint :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseLabelField
        β H Ω D false false true Sh.four_endpoint labelEndpoint)
    (hfourOrigin :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseLabelField
        β H Ω D false true false Sh.four_origin labelOrigin)
    (hfourOriginEndpoint :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseLabelField
        β H Ω D false true true Sh.four_origin_endpoint
        labelOriginEndpoint)
    (hfourGhost :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseLabelField
        β H Ω D true false false Sh.four_ghost labelGhost)
    (hfourGhostEndpoint :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseLabelField
        β H Ω D true false true Sh.four_ghost_endpoint
        labelGhostEndpoint)
    (hfourGhostOrigin :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseLabelField
        β H Ω D true true false Sh.four_ghost_origin
        labelGhostOrigin)
    (hfourGhostOriginEndpoint :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseLabelField
        β H Ω D true true true Sh.four_ghost_origin_endpoint
        labelGhostOriginEndpoint) :
    Sh.SupportResidualCaseFieldwiseLeMul β H Ω D := by
  refine
    ⟨hzeroNone, htwoNone, htwoEndpoint, htwoOrigin, htwoGhost,
      htwoGhostEndpoint, htwoGhostOrigin, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases hfourNone k hk with ⟨labelShare, hshare, hcases⟩
    refine ⟨fun R => ∑ i : ι, labelShare R i, hshare, ?_⟩
    intro R hR
    exact
      sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := false) (hasOrigin := false) (hasEndpoint := false)
        (R := R) (label := labelNone R) (labelShare := labelShare R)
        (hcases R hR)
  · intro k hk
    rcases hfourEndpoint k hk with ⟨labelShare, hshare, hcases⟩
    refine ⟨fun R => ∑ i : ι, labelShare R i, hshare, ?_⟩
    intro R hR
    exact
      sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := false) (hasOrigin := false) (hasEndpoint := true)
        (R := R) (label := labelEndpoint R) (labelShare := labelShare R)
        (hcases R hR)
  · intro k hk
    rcases hfourOrigin k hk with ⟨labelShare, hshare, hcases⟩
    refine ⟨fun R => ∑ i : ι, labelShare R i, hshare, ?_⟩
    intro R hR
    exact
      sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := false) (hasOrigin := true) (hasEndpoint := false)
        (R := R) (label := labelOrigin R) (labelShare := labelShare R)
        (hcases R hR)
  · intro k hk
    rcases hfourOriginEndpoint k hk with
      ⟨labelShare, hshare, hcases⟩
    refine ⟨fun R => ∑ i : ι, labelShare R i, hshare, ?_⟩
    intro R hR
    exact
      sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := false) (hasOrigin := true) (hasEndpoint := true)
        (R := R) (label := labelOriginEndpoint R)
        (labelShare := labelShare R) (hcases R hR)
  · intro k hk
    rcases hfourGhost k hk with ⟨labelShare, hshare, hcases⟩
    refine ⟨fun R => ∑ i : ι, labelShare R i, hshare, ?_⟩
    intro R hR
    exact
      sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := true) (hasOrigin := false) (hasEndpoint := false)
        (R := R) (label := labelGhost R) (labelShare := labelShare R)
        (hcases R hR)
  · intro k hk
    rcases hfourGhostEndpoint k hk with
      ⟨labelShare, hshare, hcases⟩
    refine ⟨fun R => ∑ i : ι, labelShare R i, hshare, ?_⟩
    intro R hR
    exact
      sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := true) (hasOrigin := false) (hasEndpoint := true)
        (R := R) (label := labelGhostEndpoint R)
        (labelShare := labelShare R) (hcases R hR)
  · intro k hk
    rcases hfourGhostOrigin k hk with
      ⟨labelShare, hshare, hcases⟩
    refine ⟨fun R => ∑ i : ι, labelShare R i, hshare, ?_⟩
    intro R hR
    exact
      sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := false)
        (R := R) (label := labelGhostOrigin R)
        (labelShare := labelShare R) (hcases R hR)
  · intro k hk
    rcases hfourGhostOriginEndpoint k hk with
      ⟨labelShare, hshare, hcases⟩
    refine ⟨fun R => ∑ i : ι, labelShare R i, hshare, ?_⟩
    intro R hR
    exact
      sourceClassEndpointMembershipSupportResidualExactCardResidualCaseShare_of_labelShares
        (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
        (hasGhost := true) (hasOrigin := true) (hasEndpoint := true)
        (R := R) (label := labelGhostOriginEndpoint R)
        (labelShare := labelShare R) (hcases R hR)

end Exact3D
end StatMech
