/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeDecomp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Def.StatisticalMechanics.Code.Universality.HexBridgeDecomp.Part8


namespace StatMech.Universality

open List


theorem hexHW_strictIncreasing_reverse (bs : List HexBridge) :
    StrictIncreasingWidths bs ↔ StrictDecreasingWidths bs.reverse := by
  unfold StrictIncreasingWidths StrictDecreasingWidths
  rw [List.pairwise_reverse]


end StatMech.Universality
