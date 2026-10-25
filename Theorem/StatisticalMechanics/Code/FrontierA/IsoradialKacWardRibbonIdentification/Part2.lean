/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanProduct
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


namespace GenusZeroOneRibbonComponentIdentification

theorem boundaryCoefficientFiber
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex)
    (I : GenusZeroOneRibbonComponentIdentification Component
      R C character weight conductance transport) (F : Finset E) :
    ribbonBoundaryCharacterCoefficient R character F =
      ∑ next : finiteMapFiber I.outgoingEdgeSet F,
        ∏ cycle : finiteCRSFAtomicCycle next.1,
          (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
  by_cases hF : I.supported F
  · rw [I.boundaryCoefficient_supported F hF]
    calc
      (∏ component : {component // component ∈ I.components F},
          formanCycleCoefficient (I.componentHolonomy F component)) =
        ∑ orientation :
            ({component // component ∈ I.components F} -> Bool),
          ∏ component : {component // component ∈ I.components F},
            if orientation component then
              1 - I.componentHolonomy F component
            else 1 - (I.componentHolonomy F component)⁻¹ :=
        (sum_boolOrientations_eq_prod_formanCycleCoefficient
          (fun component : {component // component ∈ I.components F} =>
            I.componentHolonomy F component)).symm
      _ = ∑ next : finiteMapFiber I.outgoingEdgeSet F,
          ∏ cycle : finiteCRSFAtomicCycle next.1,
            (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle) := by
        symm
        exact Fintype.sum_equiv (I.fiberEquivOrientations F hF)
          (fun next : finiteMapFiber I.outgoingEdgeSet F =>
            ∏ cycle : finiteCRSFAtomicCycle next.1,
              (1 - finiteCRSFAmbientAtomicCycleHolonomy transport cycle))
          (fun orientation :
              ({component // component ∈ I.components F} -> Bool) =>
            ∏ component : {component // component ∈ I.components F},
              if orientation component then
                1 - I.componentHolonomy F component
              else 1 - (I.componentHolonomy F component)⁻¹)
          (I.formanFactor_orientation F hF)
  · rw [I.boundaryCoefficient_unsupported F hF]
    letI : IsEmpty (finiteMapFiber I.outgoingEdgeSet F) :=
      I.fiberEmpty_unsupported F hF
    simp


end GenusZeroOneRibbonComponentIdentification
end StatMech.FrontierA
