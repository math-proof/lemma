/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellCount.Part2


namespace StatMech.Onsager.CellEuler

open Finset StatMech.Onsager.CellCount


def cornerDiff (S : Finset (ℤ × ℤ)) : ℤ :=
  ((cellVerts S).filter (fun v => cornerCount S v = 1)).card
    - ((cellVerts S).filter (fun v => cornerCount S v = 3)).card


end StatMech.Onsager.CellEuler
