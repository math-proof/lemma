/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part14


namespace StatMech.Universality

open HexWalk

noncomputable section

def hlhd_coreTurns (entry : ℤ) (raw : List ℤ) : List ℤ :=
  entry :: raw.tail


def hlhd_endpointTurns (exits : Bool) (exitTurn : ℤ)
    (core : List ℤ) : List ℤ :=
  if exits then core ++ [exitTurn] else core


def hlhd_decodeColumn (tag : HLHDColumnTag) (out : List ℤ) : List ℤ :=
  hlhd_bitTurn tag.firstPositive ::
    (if tag.exits then out.dropLast else out).tail

end
end StatMech.Universality
