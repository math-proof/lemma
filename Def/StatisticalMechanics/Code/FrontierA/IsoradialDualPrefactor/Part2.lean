/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

namespace RibbonPermutationSystem

noncomputable def dualRibbonSystem
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) : RibbonPermutationSystem E D where
  rotation := R.boundaryPerm Finset.univ
  edgeFlip := R.edgeFlip
  edgeFlip_isSwap := R.edgeFlip_isSwap
  edgeFlip_commute := R.edgeFlip_commute

end RibbonPermutationSystem
end StatMech.FrontierA
