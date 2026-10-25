/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanProduct
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part6


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


structure CriticalIsoradialEmbeddingRibbonCertificate
    (Component : Type*) [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool) where
  componentIdentification :
    GenusZeroOneRibbonComponentIdentification Component R C character
      (fun e => isoradialCriticalMu (thetaEdge e))
      (isoradialMuConductance thetaVertex) transport
  coefficientIdentification :
    CriticalKacWardRibbonCoefficientIdentification
      R character kacWard thetaEdge exceptional


end StatMech.FrontierA
