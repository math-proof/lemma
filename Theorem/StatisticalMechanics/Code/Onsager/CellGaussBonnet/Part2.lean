/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3
import Def.StatisticalMechanics.Code.Onsager.CellGaussBonnet


namespace StatMech.Onsager.CellGaussBonnet

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


theorem localIdentity_stated_false :
    ¬ ∀ e w n s ne nw se sw : Bool,
      lhsLocal e w n s ne nw se sw = rhsStated e w n s ne nw se sw := by
  intro h
  have := h false false false false false false false true
  simp only [lhsLocal, rhsStated, deltaV, deltaE, bI, ijump, icw, isZero] at this
  norm_num at this


end StatMech.Onsager.CellGaussBonnet
