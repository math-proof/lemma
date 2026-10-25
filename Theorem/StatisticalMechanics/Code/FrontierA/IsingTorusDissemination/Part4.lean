/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusDissemination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part10
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusCharacter.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusDissemination.Part4
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


theorem isingTorusDisseminatedBlock_one
    (i : Fin d) (h : IsingDyadicTorus d k → Real) :
    IsingTorusDisseminatedBlock i 1 h := by
  intro x hx
  have hxi : x i = 0 := by
    apply (ZMod.val_eq_zero (x i)).mp
    omega
  congr 1
  symm
  simpa [hxi] using (Function.update_eq_self i x)

theorem isingTorus_side_eq_two_mul_half' :
    2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by
  rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring


end StatMech.FrontierA
