/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/CellEuler.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.CellCount.Part2
import Theorem.StatisticalMechanics.Code.Onsager.CellEuler


namespace StatMech.Onsager.CellEuler

open Finset StatMech.Onsager.CellCount


def cornerWeight (k : ℕ) : ℤ := (if k = 1 then 1 else 0) - (if k = 3 then 1 else 0)


end StatMech.Onsager.CellEuler
