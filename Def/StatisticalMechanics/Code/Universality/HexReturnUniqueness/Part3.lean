/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexReturnUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexConcreteRegion.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part5
import Structure.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part2


namespace StatMech.Universality

open Complex HexWalk


def hexReturnState (d : HexReturnCoord) : List ℤ → HexReturnState
  | [] => ⟨HexReturnCoord.zero, d⟩
  | t :: ts =>
      let e := d.turn t
      let r := hexReturnState e ts
      ⟨d.add (e.add r.displacement), r.direction⟩


end StatMech.Universality
