/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardRibbonIdentification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardFormanProduct
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part2


namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {V E D Q : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]
  [Fintype Q] [DecidableEq Q]


namespace GenusZeroOneRibbonComponentIdentification

noncomputable def toFormanIdentification
    {Component : Type*} [Fintype Component] [DecidableEq Component]
    (R : RibbonPermutationSystem E D) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (weight : E -> Complex) (conductance transport : V -> V -> Complex)
    (I : GenusZeroOneRibbonComponentIdentification Component
      R C character weight conductance transport) :
    GenusZeroOneRibbonFormanIdentification
      R C character weight conductance transport where
  genus_le_one := I.genus_le_one
  outgoingEdgeSet := I.outgoingEdgeSet
  conductanceMonomial := I.conductanceMonomial
  boundaryCoefficientFiber :=
    I.boundaryCoefficientFiber R C character weight conductance transport

end GenusZeroOneRibbonComponentIdentification
end StatMech.FrontierA
