/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanProduct
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part4


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


theorem criticalKacWard_det_eq_laplacian_of_ribbonIdentification
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool)
    (I : GenusZeroOneRibbonFormanIdentification R C character
      (fun e => isoradialCriticalMu (thetaEdge e))
      (isoradialMuConductance thetaVertex) transport)
    (K : CriticalKacWardRibbonExpansion
      R character kacWard thetaEdge exceptional) :
    (1 - kacWard).det =
      (-1 : Complex) ^ coneExceptionCount exceptional *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det := by
  rw [K.expansion,
    I.ribbonSubgraphSum_eq_laplacianDet,
    det_finiteTwistedLaplacian_isoradialMu]
  calc
    ((-1 : Complex) ^ Fintype.card V *
          kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
          (∏ v : V, coneQuarterPhase exceptional v) *
          kwLaplacianEdgePrefactor thetaEdge) *
        (Complex.I ^ Fintype.card V *
          (finiteTwistedLaplacian
            (isoradialLaplacianConductance thetaVertex) transport).det) =
      (((-1 : Complex) ^ Fintype.card V *
          (∏ v : V, coneQuarterPhase exceptional v) *
          Complex.I ^ Fintype.card V) *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det) := by
      ring
    _ = _ := by rw [conePhase_prefactor_eq_exceptionSign]

omit [DecidableEq E] in


theorem criticalKacWard_det_eq_laplacian_of_componentIdentification
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool)
    (I : GenusZeroOneRibbonComponentIdentification Component R C character
      (fun e => isoradialCriticalMu (thetaEdge e))
      (isoradialMuConductance thetaVertex) transport)
    (K : CriticalKacWardRibbonExpansion
      R character kacWard thetaEdge exceptional) :
    (1 - kacWard).det =
      (-1 : Complex) ^ coneExceptionCount exceptional *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det := by
  classical
  exact criticalKacWard_det_eq_laplacian_of_ribbonIdentification
    R C character kacWard thetaVertex thetaEdge transport exceptional
    (I.toFormanIdentification R C character
      (fun e => isoradialCriticalMu (thetaEdge e))
      (isoradialMuConductance thetaVertex) transport) K


theorem criticalKacWard_det_eq_laplacian_of_localIdentifications
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool)
    (I : GenusZeroOneRibbonComponentIdentification Component R C character
      (fun e => isoradialCriticalMu (thetaEdge e))
      (isoradialMuConductance thetaVertex) transport)
    (K : CriticalKacWardRibbonCoefficientIdentification
      R character kacWard thetaEdge exceptional) :
    (1 - kacWard).det =
      (-1 : Complex) ^ coneExceptionCount exceptional *
        kwEulerPowerPrefactor (Fintype.card V) (Fintype.card E) *
        kwLaplacianEdgePrefactor thetaEdge *
        (finiteTwistedLaplacian
          (isoradialLaplacianConductance thetaVertex) transport).det :=
  criticalKacWard_det_eq_laplacian_of_componentIdentification
    R C character kacWard thetaVertex thetaEdge transport exceptional I
      (K.toRibbonExpansion R character kacWard thetaEdge exceptional)


end StatMech.FrontierA
