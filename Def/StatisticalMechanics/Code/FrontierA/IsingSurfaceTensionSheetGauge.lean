/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetGauge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoundaryBridge.Part2
open Finset
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def multibondConfigXor (t s : V -> Bool) : V -> Bool :=
  fun v => (s v).xor (t v)


def multibondConfigXorEquiv (t : V -> Bool) :
    (V -> Bool) ≃ (V -> Bool) where
  toFun := multibondConfigXor t
  invFun := multibondConfigXor t
  left_inv s := by
    funext v
    simp [multibondConfigXor, Bool.xor_assoc]
  right_inv s := by
    funext v
    simp [multibondConfigXor, Bool.xor_assoc]


end
end StatMech.FrontierA
