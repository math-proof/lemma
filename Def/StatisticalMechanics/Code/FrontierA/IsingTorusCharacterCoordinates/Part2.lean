module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacterCoordinates
open Finset
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacterCoordinates.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

variable {d k : Nat}


noncomputable def isingTorusMomentumEquiv :
    IsingDyadicTorus d k ≃
      AddChar (IsingDyadicTorus d k) Complex := by
  apply Equiv.ofBijective isingTorusMomentumChar
  rw [Fintype.bijective_iff_injective_and_card]
  exact ⟨isingTorusMomentumChar_injective, AddChar.card_eq.symm⟩

end StatMech.FrontierA
