/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointVertex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointWalk.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexReturnUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexStripBandClose.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexAllWidthStripGeometry.Part18
import Structure.StatisticalMechanics.Code.Universality.HexEndpointVertex


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

def hexEndpointCoordRun : HexReturnCoord → HexReturnCoord → List ℤ →
    HexEndpointCoordRun
  | p, d, [] => ⟨p, d⟩
  | p, d, t :: ts =>
      let e := d.turn t
      hexEndpointCoordRun (p.add e) e ts


def HexReturnCoord.IsEvenDir (d : HexReturnCoord) : Prop :=
  d = ⟨1, 0⟩ ∨ d = ⟨0, 1⟩ ∨ d = ⟨-1, -1⟩


def HexReturnCoord.IsOddDir (d : HexReturnCoord) : Prop :=
  d = ⟨1, 1⟩ ∨ d = ⟨-1, 0⟩ ∨ d = ⟨0, -1⟩


def HexEndpointCoordRun.ColorCompatible (s : HexEndpointCoordRun) : Prop :=
  (s.dir.IsEvenDir ∧ (3 : ℤ) ∣ s.pos.x + s.pos.y) ∨
    (s.dir.IsOddDir ∧ (3 : ℤ) ∣ s.pos.x + s.pos.y + 1)

end
end StatMech.Universality
