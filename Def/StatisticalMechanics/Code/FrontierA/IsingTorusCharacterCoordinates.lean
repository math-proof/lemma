/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusCharacterCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

variable {d k : Nat}


noncomputable def isingTorusMomentumChar
    (p : IsingDyadicTorus d k) :
    AddChar (IsingDyadicTorus d k) Complex where
  toFun x := ∏ i : Fin d, ZMod.stdAddChar (p i * x i)
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by
    intro x y
    simp only [Pi.add_apply, mul_add, AddChar.map_add_eq_mul,
      Finset.prod_mul_distrib]

end StatMech.FrontierA
