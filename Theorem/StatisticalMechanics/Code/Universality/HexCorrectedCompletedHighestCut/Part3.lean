/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedCompletedHighestCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.HexCorrectedSideDepth
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedShiftedDivergence
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExteriorPeriod.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepthCompletion.Part8
import Def.StatisticalMechanics.Code.Universality.HexCorrectedCompletedHighestCut.Part3


namespace StatMech.Universality

open HexWalk

noncomputable section

theorem hexCS_completedHighestCut_recurrence
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    ∀ T, 1 ≤ T →
      hexCSInfiniteSideMassAtWidth (T + 1) -
          hexCSInfiniteSideMassAtWidth T ≤
        (hexChiE⁻¹ ^ 5) *
          (hexCSInfiniteTopMassAtWidth (T + 2) *
            hexCSInfiniteTopMassAtWidth (T + 2)) := by
  intro T hT
  have hbound := (hexCSCompletedAsymmetricCut T hT hwalk).recursion_bound
    (le_of_lt (pow_pos hexChiE_inv_pos 5))
  rw [show (∑' d, (hexCSCompletedAsymmetricCut T hT hwalk).wtγ d) =
      hexCSInfiniteSideMassAtWidth (T + 1) -
        hexCSInfiniteSideMassAtWidth T from
      hexCSNewSide_tsum_eq_difference T hT hwalk,
    show (∑' b, (hexCSCompletedAsymmetricCut T hT hwalk).wtB₁ b) =
      hexCSInfiniteTopMassAtWidth (T + 2) from
      hexCSCompletedTop_tsum_eq_mass T hT,
    show (∑' b, (hexCSCompletedAsymmetricCut T hT hwalk).wtB₂ b) =
      hexCSInfiniteTopMassAtWidth (T + 2) from
      hexCSCompletedTop_tsum_eq_mass T hT] at hbound
  exact hbound


theorem hexCS_critical_divergence_of_completedHighestCut
    (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT) :
    ¬ Summable
      (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) := by
  apply hexCS_critical_divergence_of_shifted_recurrence
    (hexChiE⁻¹ ^ 5) (pow_pos hexChiE_inv_pos 5)
    2 2 (by omega) (by omega)
    hlocal hexCSBoundaryWindowLaw_unconditional
    hexCS_completedHighestCut_recurrence
    hexCSTopWalkAtWidth_one_nonempty

end
end StatMech.Universality
