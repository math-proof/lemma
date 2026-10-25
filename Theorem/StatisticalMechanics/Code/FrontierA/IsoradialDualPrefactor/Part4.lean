/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part3


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

namespace RibbonPermutationSystem

@[simp]
theorem dualBoundaryCharacter_reverse
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (F : Finset E) (boundary : Fin (R.dualRibbonSystem.boundaryComponents F)) :
    R.dualBoundaryCharacter character F boundary =
      (character Fᶜ
        (R.dualBoundaryIdentification.boundaryEquiv F boundary))⁻¹ := rfl

end RibbonPermutationSystem


theorem ribbonBoundaryCharacterCoefficient_dual
    {Dprimal Ddual : Type*}
    [Fintype Dprimal] [DecidableEq Dprimal]
    [Fintype Ddual] [DecidableEq Ddual]
    (primalRibbon : RibbonPermutationSystem E Dprimal)
    (dualRibbon : RibbonPermutationSystem E Ddual)
    (identification : RibbonDualBoundaryIdentification
      primalRibbon dualRibbon)
    (primalCharacter : forall F : Finset E,
      Fin (primalRibbon.boundaryComponents F) -> Complex)
    (dualCharacter : forall F : Finset E,
      Fin (dualRibbon.boundaryComponents F) -> Complex)
    (character_reverse : forall (F : Finset E)
      (boundary : Fin (dualRibbon.boundaryComponents F)),
      dualCharacter F boundary =
        (primalCharacter Fᶜ (identification.boundaryEquiv F boundary))⁻¹)
    (F : Finset E) :
    ribbonBoundaryCharacterCoefficient dualRibbon dualCharacter F =
      dualRibbonBoundaryCharacterCoefficient primalRibbon primalCharacter F := by
  unfold ribbonBoundaryCharacterCoefficient
    dualRibbonBoundaryCharacterCoefficient
  apply Fintype.prod_equiv (identification.boundaryEquiv F)
  intro boundary
  rw [character_reverse]


theorem dualBoundaryCharacterCoefficient_eq
    {D : Type*} [Fintype D] [DecidableEq D]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (F : Finset E) :
    ribbonBoundaryCharacterCoefficient R.dualRibbonSystem
        (R.dualBoundaryCharacter character) F =
      dualRibbonBoundaryCharacterCoefficient R character F :=
  ribbonBoundaryCharacterCoefficient_dual R R.dualRibbonSystem
    R.dualBoundaryIdentification character
    (R.dualBoundaryCharacter character)
    (R.dualBoundaryCharacter_reverse character) F

end StatMech.FrontierA
