/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part13


namespace StatMech.Universality

open HexWalk

noncomputable section

def hlhd_turnBit (t : ℤ) : Bool := decide (t = 1)

def hlhd_bitTurn (b : Bool) : ℤ := if b then 1 else -1

end
end StatMech.Universality
