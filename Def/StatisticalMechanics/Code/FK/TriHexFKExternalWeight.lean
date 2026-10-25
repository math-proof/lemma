/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKExternalWeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriHexFKStarTriangle
open Finset
open scoped BigOperators


namespace StatMech

namespace FK

namespace PeriodicPlanar

def triangleFKTerminalWeightedSum
    (y0 y1 y2 : Real) (external : ThreeTerminalConnectivity → Real) : Real :=
  ∑ c, external c * triangleFKTerminalWeight y0 y1 y2 c


def starFKTerminalWeightedSum
    (q y0 y1 y2 : Real) (external : ThreeTerminalConnectivity → Real) : Real :=
  ∑ c, external c * starFKTerminalWeight q y0 y1 y2 c


noncomputable def triangleFKTerminalWeightedRatio
    (y0 y1 y2 : Real) (external observable : ThreeTerminalConnectivity → Real) : Real :=
  triangleFKTerminalWeightedSum y0 y1 y2
      (fun c ↦ external c * observable c) /
    triangleFKTerminalWeightedSum y0 y1 y2 external


noncomputable def starFKTerminalWeightedRatio
    (q y0 y1 y2 : Real)
    (external observable : ThreeTerminalConnectivity → Real) : Real :=
  starFKTerminalWeightedSum q y0 y1 y2
      (fun c ↦ external c * observable c) /
    starFKTerminalWeightedSum q y0 y1 y2 external


end PeriodicPlanar
end FK
end StatMech
