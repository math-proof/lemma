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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part124
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15NormalizedRowsRawTotal_of_labelFreeRawTotal
    {ι :
      (n : ℕ) →
        FK.boxVerts 3 n →
          Bool → Bool → Bool →
            Finset (Option (FK.boxVerts 3 n)) → Type*}
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      Fintype (ι n v hasGhost hasOrigin hasEndpoint R)]
    [∀ n v hasGhost hasOrigin hasEndpoint R,
      DecidableEq (ι n v hasGhost hasOrigin hasEndpoint R)]
    {label :
      ∀ {n : ℕ},
        Finset
          (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ) →
        (v : FK.boxVerts 3 n) →
        ∀ hasGhost hasOrigin hasEndpoint R,
          finiteBoundaryGhostSigmaFullSourceClassifiedTwoPointSourceData n v →
            ι n v hasGhost hasOrigin hasEndpoint R}
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawTotalWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15NormalizedRowsRawTotalWeightNonzeroPositiveSubcritical
      ι label := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have hlabelFree :
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
          v β H Ωnz ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v := by
    simpa [Ωnz] using hn H hH Ω v hv
  have hraw :
      SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
          v β H Ωnz (ι n v) (label Ωnz v) =
        SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
          v β H Ωnz := by
    simpa [Ωnz] using
      (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal_eq_labelFreeRawTotal
        (v := v) (β := β) (H := H) (Ω := Ωnz)
        (ι := ι n v) (label := label Ωnz v))
  simpa [Ωnz, hraw] using hlabelFree

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15_of_labelFreeRawTotal
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawTotalWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15WeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [h β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  have hlabelFree :
      SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
          v β H Ωnz ≤
        finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile β H n Ωnz v -
          finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
            β H n Ωnz v := by
    simpa [Ωnz] using hn H hH Ω v hv
  have hshellEq :
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ωnz v).total =
        SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
          v β H Ωnz := by
    calc
      (finiteBoundaryGhostSourceClassEndpointMembershipResidualThresholdShellBudget15
        β H n Ωnz v).total =
          SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal
            v β H Ωnz (fun _ _ _ _ => Unit)
              (fun _ _ _ _ _ => ()) := by
        simpa [Ωnz] using
          (SourceClassEndpointMembershipResidualShellShare15.residualThresholdShellBudget15_total_eq_normalizedRowsRawTotal_of_boundary
            β H n Ωnz v hv (fun _ _ _ _ _ => ()))
      _ =
          SourceClassEndpointMembershipResidualShellShare15.labelFreeRawTotal
            v β H Ωnz := by
        simpa [Ωnz] using
          (SourceClassEndpointMembershipResidualShellShare15.normalizedRowsRawTotal_eq_labelFreeRawTotal
            (v := v) (β := β) (H := H) (Ω := Ωnz)
            (ι := fun _ _ _ _ => Unit)
            (label := fun _ _ _ _ _ => ()))
  simpa [Ωnz, hshellEq] using hlabelFree

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawTotal
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawTotalWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_residualThresholdShellBudget15
    (inactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15_of_labelFreeRawTotal
      h)

set_option linter.style.longLine false in


theorem boundaryVertexDecrementedSourceProfileMajorization_of_labelFreeRawTotal
    (h :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackResidualThresholdShellBudget15LabelFreeRawTotalWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceProfileMajorizationPositiveSubcritical :=
  boundaryVertexDecrementedSourceProfileMajorization_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
    (inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_labelFreeRawTotal h)

end Exact3D
end StatMech
