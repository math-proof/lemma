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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part122
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdBudget15_of_residualThresholdShellBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdBudget15WeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let B :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15
      β H n Ωnz v
  let Bshell :=
    finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
      β H n Ωnz v
  have hshell :
      Bshell.total ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v := by
    simpa [Ωnz, Bshell] using hn H hH Ω v hv
  have hfield :
      SourceClassEndpointMembershipLiveBudget15.FieldwiseLe B Bshell := by
    refine
      ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
    · simp [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
    · simp [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
    · simp [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
    · simp [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
    · simp [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
    · simp [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15]
    · simpa [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v false false false
    · simpa [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v false false true
    · simpa [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v false true false
    · simpa [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v false true true
    · simpa [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v true false false
    · simpa [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v true false true
    · simpa [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v true true false
    · simpa [B, Bshell,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15,
        finiteBoundaryGhostSourceClassEndpointMembershipAuxiliaryTwoSourceBudget15] using
        finiteBoundaryGhostSourceClassEndpointMembershipMarkedResidualThresholdImageSourceClassSum_le_thresholdShellImageSourceClassSum
          (le_of_lt hβpos) (le_of_lt hH) n Ωnz v true true true
  have hthreshold :
      B.total ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v :=
    (SourceClassEndpointMembershipLiveBudget15.total_le_of_fieldwiseLe hfield).trans
      hshell
  simpa [Ωnz, B] using hthreshold

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_residualThresholdShellBudget15
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15WeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_residualThresholdBudget15
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdBudget15_of_residualThresholdShellBudget15
      h)

end Exact3D
end StatMech
