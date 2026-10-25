/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3


namespace StatMech.Onsager.CellGaussBonnet

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


theorem cornerDiff_cex :
    cornerDiff ({((0:ℤ), (0:ℤ)), ((1:ℤ), (1:ℤ))} : Finset (ℤ × ℤ)) = 6 := by decide


theorem eulerChar_cex :
    eulerChar ({((0:ℤ), (0:ℤ)), ((1:ℤ), (1:ℤ))} : Finset (ℤ × ℤ)) = 1 := by decide


theorem gaussBonnet_stated_false :
    ¬ ∀ S : Finset (ℤ × ℤ), cornerDiff S = 4 * eulerChar S := by
  intro h
  have := h ({((0:ℤ), (0:ℤ)), ((1:ℤ), (1:ℤ))} : Finset (ℤ × ℤ))
  rw [cornerDiff_cex, eulerChar_cex] at this
  norm_num at this


end StatMech.Onsager.CellGaussBonnet
