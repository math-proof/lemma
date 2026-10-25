/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part4
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.Universality


def torusSiteTranslateEquiv (L : ℕ) (t : Site 2) :
    (ZMod L × ZMod L) ≃ (ZMod L × ZMod L) where
  toFun z := (z.1 + (t 0 : ZMod L), z.2 + (t 1 : ZMod L))
  invFun z := (z.1 - (t 0 : ZMod L), z.2 - (t 1 : ZMod L))
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

end StatMech.BeffaraDC
