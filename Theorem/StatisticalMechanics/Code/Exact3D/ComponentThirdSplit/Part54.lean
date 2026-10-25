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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part56
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15_total
    {β H : ℝ} {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n} :
    (SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15
        v β H Ω).total =
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
        v β H Ω := by
  simp [
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15,
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal,
    SourceClassEndpointMembershipLiveBudget15.total]

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal_eq_labelFreeRawTotal
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
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
        v β H Ω ι label =
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
        v β H Ω := by
  simp [
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal,
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal,
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawFourShare_eq_labelFreeRawFourShare]

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_total
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
    (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
        v β H Ω ι label).total =
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
        v β H Ω ι label := by
  rfl

set_option linter.style.longLine false in


theorem SourceClassEndpointMembershipResidualShellShare15.residualThresholdShellBudget15_total_eq_normalizedRowsRawTotal_of_boundary
    (β H : ℝ) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n)
    (hv : v ∈ Finset.univ.filter (FK.boxBoundary 3 n))
    {ι :
      Bool → Bool → Bool →
        Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ hasGhost hasOrigin hasEndpoint R,
      Fintype (ι hasGhost hasOrigin hasEndpoint R)]
    [∀ hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι hasGhost hasOrigin hasEndpoint R)]
    (label :
      ∀ hasGhost hasOrigin hasEndpoint R,
        finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
          ι hasGhost hasOrigin hasEndpoint R) :
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).total =
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
        v β H Ω ι label := by
  let rawBudget :=
    SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15
      v β H Ω ι label
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ω v
  have hEq : rawBudget = B := by
    simpa [rawBudget, B] using
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_eq_residualThresholdShellBudget15_of_boundary
        β H n Ω v hv label
  have htotal :
      rawBudget.total =
        SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
          v β H Ω ι label := by
    simpa [rawBudget] using
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawBudget15_total
        (v := v) (β := β) (H := H) (Ω := Ω)
        (ι := ι) (label := label)
  calc
    (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v).total = B.total := by rfl
    _ = rawBudget.total := by rw [hEq]
    _ =
        SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
          v β H Ω ι label := htotal

end Exact3D
end StatMech
