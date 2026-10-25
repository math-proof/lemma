/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellGaussBonnet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler.Part3
import Def.StatisticalMechanics.Code.Onsager.CellGaussBonnet.Part2


namespace StatMech.Onsager.CellGaussBonnet

open Finset StatMech.Onsager.CellCount StatMech.Onsager.CellEuler


theorem localIdentity_corrected :
    ∀ e w n s ne nw se sw : Bool,
      lhsLocal e w n s ne nw se sw = rhsCorrected e w n s ne nw se sw := by
  decide

end StatMech.Onsager.CellGaussBonnet
