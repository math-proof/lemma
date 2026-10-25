/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part5


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

structure IsoradialDualConePhaseBalance
    (PrimalVertex DualVertex : Type*)
    [Fintype PrimalVertex] [Fintype DualVertex]
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool) where
  dualVertexCount_eq : C.dualVertexCount = Fintype.card DualVertex
  phaseBalance :
    (∏ vertex : DualVertex, coneQuarterPhase dualExceptional vertex) *
        (-Complex.I) ^ Fintype.card E =
      (-1 : Complex) ^ Fintype.card PrimalVertex *
        ∏ vertex : PrimalVertex,
          coneQuarterPhase primalExceptional vertex


structure IsoradialDualGaussBonnetParity
    (PrimalVertex DualVertex : Type*)
    [Fintype PrimalVertex] [Fintype DualVertex]
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool) where
  primalVertexCount_eq : C.primalVertexCount = Fintype.card PrimalVertex
  dualVertexCount_eq : C.dualVertexCount = Fintype.card DualVertex
  exceptionParity :
    (coneExceptionCount primalExceptional +
      coneExceptionCount dualExceptional + 1) % 2 = C.genus % 2


structure IsoradialOddConeGaussBonnetData
    (PrimalVertex DualVertex : Type*)
    [Fintype PrimalVertex] [Fintype DualVertex]
    {Dart : Type*} [Fintype Dart] [DecidableEq Dart]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool) where
  primalVertexCount_eq : C.primalVertexCount = Fintype.card PrimalVertex
  dualVertexCount_eq : C.dualVertexCount = Fintype.card DualVertex
  primalConeIndex : PrimalVertex -> Nat
  dualConeIndex : DualVertex -> Nat
  primalExceptional_iff : forall vertex,
    primalExceptional vertex = true ↔ primalConeIndex vertex % 2 = 1
  dualExceptional_iff : forall vertex,
    dualExceptional vertex = true ↔ dualConeIndex vertex % 2 = 1
  coneIndexGaussBonnet :
    (∑ vertex : PrimalVertex, primalConeIndex vertex) +
      (∑ vertex : DualVertex, dualConeIndex vertex) + 1 = C.genus

end StatMech.FrontierA
