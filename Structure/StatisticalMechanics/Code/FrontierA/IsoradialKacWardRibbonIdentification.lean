/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanProduct
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


structure GenusZeroOneRibbonComponentIdentification
    (Component : Type*) [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex) where
  genus_le_one : C.genus <= 1
  outgoingEdgeSet : (V -> V) -> Finset E
  conductanceMonomial : forall next : V -> V,
    finiteCRSFOutgoingConductance conductance next =
      ∏ e ∈ outgoingEdgeSet next, weight e
  supported : Finset E -> Prop
  components : Finset E -> Finset Component
  componentHolonomy : Finset E -> Component -> Complex
  boundaryCoefficient_supported : forall (F : Finset E), supported F ->
    ribbonBoundaryCharacterCoefficient R character F =
      ∏ component : {component // component ∈ components F},
        formanCycleCoefficient (componentHolonomy F component)
  boundaryCoefficient_unsupported : forall (F : Finset E), ¬ supported F ->
    ribbonBoundaryCharacterCoefficient R character F = 0
  fiberEmpty_unsupported : forall (F : Finset E), ¬ supported F ->
    IsEmpty (finiteMapFiber outgoingEdgeSet F)
  fiberEquivOrientations : forall (F : Finset E), supported F ->
    finiteMapFiber outgoingEdgeSet F ≃
      ({component // component ∈ components F} -> Bool)
  formanFactor_orientation : forall (F : Finset E) (hF : supported F)
      (next : finiteMapFiber outgoingEdgeSet F),
    (∏ cycle : finiteCRSFAtomicCycle next.1,
        (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle)) =
      ∏ component : {component // component ∈ components F},
        if (fiberEquivOrientations F hF next) component then
          1 - componentHolonomy F component
        else 1 - (componentHolonomy F component)⁻¹


structure GenusZeroOneRibbonFormanIdentification
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex) where
  genus_le_one : C.genus <= 1
  outgoingEdgeSet : (V -> V) -> Finset E
  conductanceMonomial : forall next : V -> V,
    finiteCRSFOutgoingConductance conductance next =
      ∏ e ∈ outgoingEdgeSet next, weight e
  boundaryCoefficientFiber : forall F : Finset E,
    ribbonBoundaryCharacterCoefficient R character F =
      ∑ next : finiteMapFiber outgoingEdgeSet F,
        ∏ cycle : finiteCRSFAtomicCycle next.1,
          (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle)

end StatMech.FrontierA
