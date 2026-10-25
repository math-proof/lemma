/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3
import Theorem.StatisticalMechanics.Code.Onsager.CellGaussBonnet


namespace StatMech.Onsager.CellGaussBonnet

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


def bI (b : Bool) : ℤ := if b then 1 else 0


def icw (k : ℤ) : ℤ := (if k = 1 then 1 else 0) - (if k = 3 then 1 else 0)


def ijump (m : ℤ) : ℤ := icw (m + 1) - icw m


def isZero (m : ℤ) : ℤ := if m = 0 then 1 else 0


def lhsLocal (e w n s ne nw se sw : Bool) : ℤ :=
  ijump (bI w + bI s + bI sw) + ijump (bI e + bI se + bI s)
    + ijump (bI n + bI nw + bI w) + ijump (bI ne + bI n + bI e)


def deltaV (e w n s ne nw se sw : Bool) : ℤ :=
  isZero (bI w + bI s + bI sw) + isZero (bI e + bI se + bI s)
    + isZero (bI n + bI nw + bI w) + isZero (bI ne + bI n + bI e)


def deltaE (e w n s : Bool) : ℤ :=
  (1 - bI s) + (1 - bI n) + (1 - bI w) + (1 - bI e)


def rhsStated (e w n s ne nw se sw : Bool) : ℤ :=
  4 * (deltaV e w n s ne nw se sw - deltaE e w n s + 1)


end StatMech.Onsager.CellGaussBonnet
