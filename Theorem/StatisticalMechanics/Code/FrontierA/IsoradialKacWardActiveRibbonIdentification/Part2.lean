/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardActiveRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialKacWardActiveRibbonIdentification


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


namespace GenusZeroOneActiveRibbonFormanIdentification

theorem ribbonSubgraphSum_eq_laplacianDet
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex)
    (I : GenusZeroOneActiveRibbonFormanIdentification
      R C character weight conductance transport) :
    kwDualSubgraphSum
        (ribbonBoundaryCharacterCoefficient R character) weight =
      (finiteTwistedLaplacian conductance transport).det := by
  rw [det_finiteTwistedLaplacian_eq_sum_outgoing_mul_formanProduct]
  unfold kwDualSubgraphSum
  change (∑ F : Finset E,
      ribbonBoundaryCharacterCoefficient R character F *
        ∏ e ∈ F, weight e) =
    ∑ next : V -> V,
      finiteCRSFOutgoingConductance conductance next *
        finiteCRSFFormanProduct transport next
  calc
    (∑ F : Finset E,
        ribbonBoundaryCharacterCoefficient R character F *
          ∏ e ∈ F, weight e) =
      ∑ F : Finset E,
        (∑ next : finiteMapFiber I.outgoingEdgeSet F,
          finiteCRSFFormanProduct transport next.1) *
            ∏ e ∈ F, weight e := by
      apply Finset.sum_congr rfl
      intro F _
      rw [I.boundaryCoefficientFiber F]
    _ = ∑ F : Finset E,
        ∑ next : finiteMapFiber I.outgoingEdgeSet F,
          finiteCRSFOutgoingConductance conductance next.1 *
            finiteCRSFFormanProduct transport next.1 := by
      apply Finset.sum_congr rfl
      intro F _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro next _
      by_cases hactive : finiteCRSFFormanProduct transport next.1 = 0
      · simp [hactive]
      · rw [I.conductanceMonomial next.1 hactive, next.2]
        ring
    _ = ∑ next : V -> V,
        finiteCRSFOutgoingConductance conductance next *
          finiteCRSFFormanProduct transport next := by
      exact Fintype.sum_fiberwise I.outgoingEdgeSet
        (fun next : V -> V =>
          finiteCRSFOutgoingConductance conductance next *
            finiteCRSFFormanProduct transport next)

end GenusZeroOneActiveRibbonFormanIdentification


theorem criticalKacWard_det_eq_laplacian_of_activeRibbonIdentification
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex)
    (thetaVertex : V -> V -> Real) (thetaEdge : E -> Real)
    (transport : V -> V -> Complex) (exceptional : V -> Bool)
    (I : GenusZeroOneActiveRibbonFormanIdentification R C character
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

end StatMech.FrontierA
