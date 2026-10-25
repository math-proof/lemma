/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardActiveRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardActiveRibbonIdentification


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


structure GenusZeroOneActiveRibbonFormanIdentification
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex) where
  genus_le_one : C.genus <= 1
  outgoingEdgeSet : (V -> V) -> Finset E
  conductanceMonomial : forall next : V -> V,
    finiteCRSFFormanProduct transport next ≠ 0 ->
      finiteCRSFOutgoingConductance conductance next =
        ∏ e ∈ outgoingEdgeSet next, weight e
  boundaryCoefficientFiber : forall F : Finset E,
    ribbonBoundaryCharacterCoefficient R character F =
      ∑ next : finiteMapFiber outgoingEdgeSet F,
        finiteCRSFFormanProduct transport next.1

end StatMech.FrontierA
