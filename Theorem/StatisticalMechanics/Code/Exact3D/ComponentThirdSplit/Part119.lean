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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part125
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15_of_labelFreeRawShellMajorant
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawShellMajorantWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawMajorantBudget15WeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let rawBudget :=
    SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15
      v β H Ωnz
  rcases hn H hH Ω v hv with ⟨shellMajorant, hfield, htotal⟩
  refine ⟨shellMajorant.toBudget15, ?_, ?_⟩
  · exact
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawBudget15_fieldwiseLe_toBudget15_of_labelFreeRawFieldwiseLe
        (Sh := shellMajorant) (β := β) (H := H) (Ω := Ωnz)
        hfield
  · simpa [Ωnz, rawBudget,
      SourceClassEndpointMembershipResidualShellShare15.toBudget15_total]
      using htotal

end Exact3D
end StatMech
