/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanProduct
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part2


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


namespace CriticalKacWardRibbonCoefficientIdentification

omit [DecidableEq V] in


theorem expansion
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (thetaEdge : E -> Real)
    (exceptional : V -> Bool)
    (I : CriticalKacWardRibbonCoefficientIdentification
      R character kacWard thetaEdge exceptional) :
    (1 - kacWard).det =
      criticalKacWardRibbonPrefactor thetaEdge exceptional *
        kwDualSubgraphSum
          (ribbonBoundaryCharacterCoefficient R character)
          (fun e => isoradialCriticalMu (thetaEdge e)) := by
  rw [matrix_det_eq_sum_permutationTerm]
  calc
    (∑ sigma : Equiv.Perm Q,
        matrixDetPermutationTerm (1 - kacWard) sigma) =
      ∑ F : Finset E,
        ∑ sigma : finiteMapFiber I.permutationEdgeSet F,
          matrixDetPermutationTerm (1 - kacWard) sigma.1 :=
      (Fintype.sum_fiberwise I.permutationEdgeSet
        (matrixDetPermutationTerm (1 - kacWard))).symm
    _ = criticalKacWardRibbonPrefactor thetaEdge exceptional *
        kwDualSubgraphSum
          (ribbonBoundaryCharacterCoefficient R character)
          (fun e => isoradialCriticalMu (thetaEdge e)) := by
      unfold kwDualSubgraphSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F _
      rw [I.coefficientFiber F]


end CriticalKacWardRibbonCoefficientIdentification
end StatMech.FrontierA
