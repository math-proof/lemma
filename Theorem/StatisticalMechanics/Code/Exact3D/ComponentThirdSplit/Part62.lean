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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part64
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.supportResidualCasePointwiseDependentLabelField_of_normalizedRows
    {β H D : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (hDpos : 0 < D)
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {fieldShare : ℕ → ℝ}
    {ι : Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ R, Fintype (ι R)] [∀ R, DecidableEq (ι R)]
    {label :
      ∀ R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι R}
    (hfield :
      ∀ k, k ∈
          finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellIndex
            v hasGhost hasOrigin hasEndpoint →
        fieldShare k =
          ∑ R ∈
            finiteBoundaryGhostSourceClassEndpointUnmarkedResidualExactCardSet
              v k,
            ∑ i : ι R,
              ∑ E ∈
                finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
                  v Ω hasGhost hasOrigin hasEndpoint R (label R) i,
                finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand
                  β H E / D) :
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCasePointwiseDependentLabelField
      β H Ω D hasGhost hasOrigin hasEndpoint fieldShare ι label := by
  intro k hk
  refine
    ⟨fun _R E =>
        finiteBoundaryGhostSourceInactiveClassifiedCoefficientSummand β H E / D,
      hfield k hk, ?_⟩
  intro R _hR
  exact
    sourceClassEndpointMembershipSupportResidualExactCardResidualCasePointwiseShare_of_denominatorPositive
      (v := v) (β := β) (H := H) (D := D) (Ω := Ω)
      (hasGhost := hasGhost) (hasOrigin := hasOrigin)
      (hasEndpoint := hasEndpoint) (R := R)
      hβ hH hDpos

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.supportResidualCaseDependentLabelField_of_pointwiseDependentLabelField
    {β H D : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {hasGhost hasOrigin hasEndpoint : Bool}
    {fieldShare : ℕ → ℝ}
    {ι : Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ R, Fintype (ι R)] [∀ R, DecidableEq (ι R)]
    {label :
      ∀ R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι R}
    (h :
      SourceClassEndpointMembershipResidualShellShare15.SupportResidualCasePointwiseDependentLabelField
        β H Ω D hasGhost hasOrigin hasEndpoint fieldShare ι label) :
    SourceClassEndpointMembershipResidualShellShare15.SupportResidualCaseDependentLabelField
      β H Ω D hasGhost hasOrigin hasEndpoint fieldShare ι label := by
  classical
  intro k hk
  rcases h k hk with ⟨atomShare, hshare, hcases⟩
  refine
    ⟨fun R i =>
        ∑ E ∈
          finiteBoundaryGhostSourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelSet
            v Ω hasGhost hasOrigin hasEndpoint R (label R) i,
          atomShare R E,
      hshare, ?_⟩
  intro R hR
  exact
    sourceClassEndpointMembershipSupportResidualExactCardResidualCaseLabelShare_of_pointwiseShare
      (v := v) (β := β) (H := H) (Ω := Ω) (D := D)
      (hasGhost := hasGhost) (hasOrigin := hasOrigin)
      (hasEndpoint := hasEndpoint) (R := R)
      (atomShare := atomShare R) (hcases R hR)
      (label := label R)

end Exact3D
end StatMech
