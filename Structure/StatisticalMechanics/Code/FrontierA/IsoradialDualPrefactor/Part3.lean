/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part6


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

structure CriticalIsoradialDualityCertificate
    (PrimalVertex DualVertex Dart Q Qstar : Type*)
    [Fintype PrimalVertex] [Fintype DualVertex]
    [Fintype Dart] [DecidableEq Dart]
    [Fintype Q] [DecidableEq Q] [Fintype Qstar] [DecidableEq Qstar]
    (R : RibbonPermutationSystem E Dart) (C : CellularRibbonDualData R)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (theta : E -> Real)
    (primalExceptional : PrimalVertex -> Bool)
    (dualExceptional : DualVertex -> Bool)
    (primalKacWard : Matrix Q Q Complex)
    (dualKacWard : Matrix Qstar Qstar Complex) where
  theta_pos : forall edge, 0 < theta edge
  theta_lt : forall edge, theta edge < Real.pi / 2
  character_ne : forall (F : Finset E)
    (boundary : Fin (R.boundaryComponents F)), character F boundary ≠ 0
  character_total : forall F : Finset E,
    ∏ boundary, character F boundary = 1
  primalCoefficient : CriticalKacWardRibbonCoefficientIdentification
    R character primalKacWard theta primalExceptional
  dualCoefficient : CriticalKacWardRibbonCoefficientIdentification
    R.dualRibbonSystem (R.dualBoundaryCharacter character) dualKacWard
      (fun edge => Real.pi / 2 - theta edge) dualExceptional
  oddConeGaussBonnet : IsoradialOddConeGaussBonnetData
    PrimalVertex DualVertex R C primalExceptional dualExceptional


end StatMech.FrontierA
