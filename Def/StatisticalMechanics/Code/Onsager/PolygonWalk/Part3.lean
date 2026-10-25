/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/PolygonWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.PolygonWalk.Part2


namespace StatMech.Onsager.PolygonWalk

def dirCode (d : Pt) : ZMod 4 :=
  if d = (1, 0) then 0 else if d = (0, 1) then 1 else if d = (-1, 0) then 2 else 3


end StatMech.Onsager.PolygonWalk
