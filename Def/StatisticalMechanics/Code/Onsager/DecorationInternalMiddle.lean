/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationInternalMiddle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationInternalEndpoint
import Mathlib.LinearAlgebra.Matrix.SchurComplement


namespace StatMech.Onsager

open Matrix BigOperators


def ons_decMiddleSide (mu : Fin 4) : Fin 2 :=
  if mu.val < 2 then 0 else 1


def ons_decMiddleDir (side : Fin 2) : Fin 4 :=
  if side = 0 then 0 else 2

end StatMech.Onsager
