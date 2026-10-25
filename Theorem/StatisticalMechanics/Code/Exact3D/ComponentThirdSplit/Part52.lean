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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part54
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell_eq_labelFreeRawShell
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
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
          ι hasGhost hasOrigin hasEndpoint R} :
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell
        v β H Ω ι label =
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawShell
        v β H Ω := by
  unfold SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawShell
  unfold SourceClassEndpointMembershipResidualShellShare15.labelFreeRawShell
  rw [SourceClassEndpointMembershipResidualShellShare15.mk.injEq]
  refine
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext k
    exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare
        (v := v) (β := β) (H := H) (Ω := Ω) (ι := ι)
        (label := label) (hasGhost := false) (hasOrigin := false)
        (hasEndpoint := false) (k := k)
  · funext k
    exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare
        (v := v) (β := β) (H := H) (Ω := Ω) (ι := ι)
        (label := label) (hasGhost := false) (hasOrigin := false)
        (hasEndpoint := true) (k := k)
  · funext k
    exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare
        (v := v) (β := β) (H := H) (Ω := Ω) (ι := ι)
        (label := label) (hasGhost := false) (hasOrigin := true)
        (hasEndpoint := false) (k := k)
  · funext k
    exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare
        (v := v) (β := β) (H := H) (Ω := Ω) (ι := ι)
        (label := label) (hasGhost := false) (hasOrigin := true)
        (hasEndpoint := true) (k := k)
  · funext k
    exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare
        (v := v) (β := β) (H := H) (Ω := Ω) (ι := ι)
        (label := label) (hasGhost := true) (hasOrigin := false)
        (hasEndpoint := false) (k := k)
  · funext k
    exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare
        (v := v) (β := β) (H := H) (Ω := Ω) (ι := ι)
        (label := label) (hasGhost := true) (hasOrigin := false)
        (hasEndpoint := true) (k := k)
  · funext k
    exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare
        (v := v) (β := β) (H := H) (Ω := Ω) (ι := ι)
        (label := label) (hasGhost := true) (hasOrigin := true)
        (hasEndpoint := false) (k := k)
  · funext k
    exact
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare
        (v := v) (β := β) (H := H) (Ω := Ω) (ι := ι)
        (label := label) (hasGhost := true) (hasOrigin := true)
        (hasEndpoint := true) (k := k)

end Exact3D
end StatMech
