/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part34


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismThreeLayerRawMoment_eq_gram
    (beta : Real) (n : Nat) (a b : Real) :
    oddPrismThreeLayerRawMoment beta n a b =
      ∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
        oddPrismThreeLayerEndpointSum beta n a s *
        oddPrismThreeLayerEndpointSum beta n b s := by
  unfold oddPrismThreeLayerRawMoment oddPrismThreeLayerEndpointSum
  apply Finset.sum_congr rfl
  intro s _
  rw [show oddPrismLayerHalfWeight beta n s ^ 2 *
        (∑ v, oddPrismUpperConditionedVector beta n v *
          oddPrismPureSeamKernel a n s v) *
        (∑ t, oddPrismUpperConditionedVector beta n t *
          oddPrismPureSeamKernel b n s t) =
      (∑ v, oddPrismLayerHalfWeight beta n s ^ 2 *
        (oddPrismUpperConditionedVector beta n v *
          oddPrismPureSeamKernel a n s v)) *
        ∑ t, oddPrismUpperConditionedVector beta n t *
          oddPrismPureSeamKernel b n s t by
            rw [← Finset.mul_sum]]
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro t _
  ring


theorem oddPrismThreeLayerRawMoment_sq_le_diagonal
    (beta : Real) (n : Nat) (a b : Real) :
    oddPrismThreeLayerRawMoment beta n a b ^ 2 <=
      oddPrismThreeLayerRawMoment beta n a a *
        oddPrismThreeLayerRawMoment beta n b b := by
  rw [oddPrismThreeLayerRawMoment_eq_gram,
    oddPrismThreeLayerRawMoment_eq_gram,
    oddPrismThreeLayerRawMoment_eq_gram]
  let f : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real :=
    fun s => oddPrismLayerHalfWeight beta n s *
      oddPrismThreeLayerEndpointSum beta n a s
  let g : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real :=
    fun s => oddPrismLayerHalfWeight beta n s *
      oddPrismThreeLayerEndpointSum beta n b s
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset
      (ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)))) f g
  have hab : (∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
        oddPrismThreeLayerEndpointSum beta n a s *
        oddPrismThreeLayerEndpointSum beta n b s) =
      ∑ s, f s * g s := by
    apply Finset.sum_congr rfl
    intro s _
    unfold f g
    ring
  have haa : (∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
        oddPrismThreeLayerEndpointSum beta n a s *
        oddPrismThreeLayerEndpointSum beta n a s) =
      ∑ s, f s ^ 2 := by
    apply Finset.sum_congr rfl
    intro s _
    unfold f
    ring
  have hbb : (∑ s, oddPrismLayerHalfWeight beta n s ^ 2 *
        oddPrismThreeLayerEndpointSum beta n b s *
        oddPrismThreeLayerEndpointSum beta n b s) =
      ∑ s, g s ^ 2 := by
    apply Finset.sum_congr rfl
    intro s _
    unfold g
    ring
  rw [hab, haa, hbb]
  exact hcs


end
end StatMech.FrontierA
