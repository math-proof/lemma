/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusCellComplement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.BeffaraDC.TorusCellDual.Part6
open SimpleGraph Set


namespace StatMech.BeffaraDC

open StatMech.Onsager


def torusCellDiagonalShift (L : ℕ) :
    (ZMod L × ZMod L) ≃ (ZMod L × ZMod L) where
  toFun v := (v.1 + 1, v.2 + 1)
  invFun v := (v.1 - 1, v.2 - 1)
  left_inv v := by ext <;> simp
  right_inv v := by ext <;> simp

end StatMech.BeffaraDC
