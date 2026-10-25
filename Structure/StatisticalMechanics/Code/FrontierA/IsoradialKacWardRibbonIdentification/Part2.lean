/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanProduct
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part3


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


structure CriticalKacWardRibbonCoefficientIdentification
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (thetaEdge : E -> Real)
    (exceptional : V -> Bool) where
  permutationEdgeSet : Equiv.Perm Q -> Finset E
  coefficientFiber : forall F : Finset E,
    (∑ sigma : finiteMapFiber permutationEdgeSet F,
        matrixDetPermutationTerm (1 - kacWard) sigma.1) =
      criticalKacWardRibbonPrefactor thetaEdge exceptional *
        (ribbonBoundaryCharacterCoefficient R character F *
          ∏ e ∈ F, isoradialCriticalMu (thetaEdge e))


structure CriticalKacWardRibbonExpansion
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (thetaEdge : E -> Real)
    (exceptional : V -> Bool) where
  expansion :
    (1 - kacWard).det =
      (((-1 : Complex) ^ Fintype.card V *
          kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
          (∏ v : V, coneQuarterPhase exceptional v) *
          kwLaplacianEdgePrefactor thetaEdge) *
        kwDualSubgraphSum
          (ribbonBoundaryCharacterCoefficient R character)
          (fun e => isoradialCriticalMu (thetaEdge e)))

end StatMech.FrontierA
