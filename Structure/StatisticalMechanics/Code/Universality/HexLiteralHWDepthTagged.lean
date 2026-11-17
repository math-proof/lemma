/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepthTagged.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part26
public import Theorem.StatisticalMechanics.Code.Universality.HexTaggedColumnBound
public import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripColumn.Part2
public import Theorem.StatisticalMechanics.Code.Universality.HexContentHalfBound.Part3


namespace StatMech.Universality

open HexWalk

open scoped BigOperators

public noncomputable section

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
