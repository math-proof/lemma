/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskCycleTranslationHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalTransferComponentCut.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskCycleTranslationHall
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

open StatMech.Sharpness.RandomCurrent


def RightMaskCycleDifferenceRespectsCuts
    (ends : I -> Sym2 W) (m K D : Finset I) (k : W) : Prop :=
  NoCrossingK ends (K ∆ D)
      (StatMech.FrontierA.grahamComponentComplement ends K k) ∧
    NoCrossingK ends ((m \ K) ∆ D)
      (StatMech.FrontierA.grahamComponentComplement ends (m \ K) k)


end StatMech.GrahamGHS.FourColor
