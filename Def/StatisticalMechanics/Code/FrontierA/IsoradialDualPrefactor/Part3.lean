/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part3


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

namespace RibbonPermutationSystem

noncomputable def dualBoundaryIdentification
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D) :
    RibbonDualBoundaryIdentification R R.dualRibbonSystem where
  boundaryEquiv F :=
    finCongr (R.dualRibbonSystem_boundaryComponents F)


noncomputable def dualBoundaryCharacter
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (F : Finset E) (boundary : Fin (R.dualRibbonSystem.boundaryComponents F)) :
    Complex :=
  (character Fᶜ (R.dualBoundaryIdentification.boundaryEquiv F boundary))⁻¹

end RibbonPermutationSystem
end StatMech.FrontierA
