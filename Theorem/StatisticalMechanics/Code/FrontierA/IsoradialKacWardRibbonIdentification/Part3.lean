/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanProduct
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


namespace GenusZeroOneRibbonFormanIdentification

theorem ribbonSubgraphSum_eq_laplacianDet
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex)
    (I : GenusZeroOneRibbonFormanIdentification
      R C character weight conductance transport) :
    kwDualSubgraphSum
        (ribbonBoundaryCharacterCoefficient R character) weight =
      (finiteTwistedLaplacian conductance transport).det := by
  rw [det_finiteTwistedLaplacian_eq_sum_outgoing_mul_formanProduct]
  unfold kwDualSubgraphSum
  calc
    (∑ F : Finset E,
        ribbonBoundaryCharacterCoefficient R character F *
          ∏ e ∈ F, weight e) =
      ∑ F : Finset E,
        (∑ next : finiteMapFiber I.outgoingEdgeSet F,
          ∏ cycle : finiteCRSFAtomicCycle next.1,
            (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle)) *
          ∏ e ∈ F, weight e := by
      apply Finset.sum_congr rfl
      intro F _
      rw [I.boundaryCoefficientFiber F]
    _ = ∑ F : Finset E,
        ∑ next : finiteMapFiber I.outgoingEdgeSet F,
          finiteCRSFOutgoingConductance conductance next.1 *
            ∏ cycle : finiteCRSFAtomicCycle next.1,
              (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
      apply Finset.sum_congr rfl
      intro F _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro next _
      rw [I.conductanceMonomial next.1, next.2]
      ring
    _ = ∑ next : V -> V,
        finiteCRSFOutgoingConductance conductance next *
          ∏ cycle : finiteCRSFAtomicCycle next,
            (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
      exact Fintype.sum_fiberwise I.outgoingEdgeSet
        (fun next : V -> V =>
          finiteCRSFOutgoingConductance conductance next *
            ∏ cycle : finiteCRSFAtomicCycle next,
              (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle))

end GenusZeroOneRibbonFormanIdentification
end StatMech.FrontierA
