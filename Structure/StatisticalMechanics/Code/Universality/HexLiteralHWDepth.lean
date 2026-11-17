/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWDepth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWColumns.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralHWDepth.Part12


namespace StatMech.Universality

open HexWalk

public noncomputable section

structure HLHDColumnTag where
  up : Bool
  firstPositive : Bool
  exits : Bool
  deriving DecidableEq, Fintype

end
end StatMech.Universality
