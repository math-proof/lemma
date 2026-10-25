/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinWeightedTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.KWWeightedBounds
import Theorem.StatisticalMechanics.Code.Onsager.KWMultiaffineBounded
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientTarget.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SpinWeightedTarget.Part2


namespace StatMech.Onsager

open Matrix BigOperators StatMech.Ising

noncomputable def ons_spinShermanRadius (L : ℕ) : ℝ :=
  if h : 2 < L then
    letI : NeZero L := ⟨by omega⟩
    ons_ShermanRadius L
  else 1

end StatMech.Onsager
