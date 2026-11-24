module
public import Theorem.StatisticalMechanics.Code.BeffaraDC.TorusCellRN.Part5
public import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
public import Theorem.StatisticalMechanics.Code.FK.FiniteVolumeShift.Part5
open SimpleGraph Set
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/TorusSquareCrossing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.BeffaraDC

open StatMech.Onsager


def torusCoordSwap (L : ℕ) : (ZMod L × ZMod L) ≃ (ZMod L × ZMod L) where
  toFun x := (x.2, x.1)
  invFun x := (x.2, x.1)
  left_inv x := by cases x; rfl
  right_inv x := by cases x; rfl

end StatMech.BeffaraDC
