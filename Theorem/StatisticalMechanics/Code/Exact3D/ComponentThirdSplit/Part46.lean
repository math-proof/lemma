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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part48
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15_nonneg
    {β H : ℝ} (hβ : 0 ≤ β) (hH : 0 ≤ H) (n : ℕ)
    (Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ))
    (v : FK.boxVerts 3 n) :
    SourceClassEndpointMembershipLiveBudget15.Nonneg
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ω v) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
          hβ hH n Ω v ∅
  · dsimp [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
    exact Finset.sum_nonneg (fun S _hS =>
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
        hβ hH n Ω v S)
  · dsimp [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
    exact Finset.sum_nonneg (fun S _hS =>
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
        hβ hH n Ω v S)
  · dsimp [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
    exact Finset.sum_nonneg (fun S _hS =>
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
        hβ hH n Ω v S)
  · dsimp [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
    exact Finset.sum_nonneg (fun S _hS =>
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
        hβ hH n Ω v S)
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
          hβ hH n Ω v
          ({none, some v} : Finset (Option (FK.boxVerts 3 n)))
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum_nonneg
          hβ hH n Ω v
          ({none, some (IsingFK.boxOrigin 3 n)} :
            Finset (Option (FK.boxVerts 3 n)))
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_nonneg
          hβ hH n Ω v false false false
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_nonneg
          hβ hH n Ω v false false true
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_nonneg
          hβ hH n Ω v false true false
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_nonneg
          hβ hH n Ω v false true true
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_nonneg
          hβ hH n Ω v true false false
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_nonneg
          hβ hH n Ω v true false true
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_nonneg
          hβ hH n Ω v true true false
  · simpa [
      finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
      finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
      using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdShellImageSourceClassSum_nonneg
          hβ hH n Ω v true true true

end Exact3D
end StatMech
