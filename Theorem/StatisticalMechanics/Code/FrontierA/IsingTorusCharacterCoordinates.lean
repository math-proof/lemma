/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacterCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusCharacterCoordinates
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

variable {d k : Nat}


@[simp] theorem isingTorusMomentumChar_apply
    (p x : IsingDyadicTorus d k) :
    isingTorusMomentumChar p x =
      ∏ i : Fin d, ZMod.stdAddChar (p i * x i) := rfl

@[simp] theorem isingTorusMomentumChar_single
    (p : IsingDyadicTorus d k) (i : Fin d)
    (a : ZMod (2 ^ (k + 2))) :
    isingTorusMomentumChar p (Pi.single i a) =
      ZMod.stdAddChar (p i * a) := by
  rw [isingTorusMomentumChar_apply, Finset.prod_eq_single i]
  · simp [Pi.single_eq_same]
  · intro j _ hji
    simp [Pi.single_eq_of_ne hji]
  · simp

theorem isingTorusMomentumChar_injective :
    Function.Injective
      (isingTorusMomentumChar : IsingDyadicTorus d k →
        AddChar (IsingDyadicTorus d k) Complex) := by
  intro p q hpq
  funext i
  have h := DFunLike.congr_fun hpq (Pi.single i 1)
  simp only [isingTorusMomentumChar_single, mul_one] at h
  exact ZMod.injective_stdAddChar h


end StatMech.FrontierA
