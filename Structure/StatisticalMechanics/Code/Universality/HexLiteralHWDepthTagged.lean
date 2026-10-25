/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
import Theorem.StatisticalMechanics.Code.Universality.HexTaggedColumnBound
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexContentHalfBound.Part3


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

noncomputable section

structure HLHDBridgeOrigin (b : HexBridge) where
  turns : List ℤ
  legal : (ofTurns hexAWStart 1 turns).IsLegalSAW
  halfSpace : HLHDLiteralHalfSpace turns legal
  interval : ℕ × ℕ
  interval_mem : interval ∈ hlhd_intervals turns legal
  bridge_eq : b = hlhd_bridge turns legal halfSpace
    ⟨interval, interval_mem⟩

end
end StatMech.Universality
