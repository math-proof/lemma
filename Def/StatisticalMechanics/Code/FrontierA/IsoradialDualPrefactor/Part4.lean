/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part4


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

namespace CriticalKacWardRibbonCoefficientIdentification

def toSubgraphCoefficientIdentification
    {D V Q : Type*}
    [Fintype D] [DecidableEq D]
    [Fintype V]
    [Fintype Q] [DecidableEq Q]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (theta : E -> Real)
    (exceptional : V -> Bool)
    (I : CriticalKacWardRibbonCoefficientIdentification
      R character kacWard theta exceptional) :
    KacWardSubgraphCoefficientIdentification
      (ribbonBoundaryCharacterCoefficient R character) kacWard
      (fun edge => isoradialCriticalMu (theta edge))
      (criticalKacWardRibbonPrefactor theta exceptional) where
  permutationEdgeSet := I.permutationEdgeSet
  coefficientFiber := I.coefficientFiber


def toDualSubgraphCoefficientIdentification
    {Ddual Dprimal Vdual Qdual : Type*}
    [Fintype Ddual] [DecidableEq Ddual]
    [Fintype Dprimal] [DecidableEq Dprimal]
    [Fintype Vdual]
    [Fintype Qdual] [DecidableEq Qdual]
    (dualRibbon : RibbonPermutationSystem E Ddual)
    (dualCharacter : forall F : Finset E,
      Fin (dualRibbon.boundaryComponents F) -> Complex)
    (dualKacWard : Matrix Qdual Qdual Complex)
    (dualTheta : E -> Real) (dualExceptional : Vdual -> Bool)
    (I : CriticalKacWardRibbonCoefficientIdentification
      dualRibbon dualCharacter dualKacWard dualTheta dualExceptional)
    (primalRibbon : RibbonPermutationSystem E Dprimal)
    (primalCharacter : forall F : Finset E,
      Fin (primalRibbon.boundaryComponents F) -> Complex)
    (boundaryCoefficient_eq : forall F : Finset E,
      ribbonBoundaryCharacterCoefficient dualRibbon dualCharacter F =
        dualRibbonBoundaryCharacterCoefficient
          primalRibbon primalCharacter F) :
    KacWardSubgraphCoefficientIdentification
      (dualRibbonBoundaryCharacterCoefficient
        primalRibbon primalCharacter) dualKacWard
      (fun edge => isoradialCriticalMu (dualTheta edge))
      (criticalKacWardRibbonPrefactor dualTheta dualExceptional) where
  permutationEdgeSet := I.permutationEdgeSet
  coefficientFiber := by
    intro F
    rw [← boundaryCoefficient_eq F]
    exact I.coefficientFiber F

end CriticalKacWardRibbonCoefficientIdentification
end StatMech.FrontierA
