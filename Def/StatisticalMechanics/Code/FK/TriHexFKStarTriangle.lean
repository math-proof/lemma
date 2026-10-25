/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriHexFKStarTriangle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.FKTrihexDuality
import Inductive.StatisticalMechanics.Code.FK.TriHexFKStarTriangle
open Finset
open scoped BigOperators


namespace StatMech

namespace FK

namespace PeriodicPlanar

open FrontierA


def triangleFKTerminalWeight (y0 y1 y2 : Real) :
    ThreeTerminalConnectivity -> Real
  | .separate => 1
  | .pair01 => y2
  | .pair12 => y0
  | .pair20 => y1
  | .together => y0 * y1 + y1 * y2 + y2 * y0 + y0 * y1 * y2


def starFKTerminalWeight (q y0 y1 y2 : Real) :
    ThreeTerminalConnectivity -> Real
  | .separate => q + y0 + y1 + y2
  | .pair01 => y0 * y1
  | .pair12 => y1 * y2
  | .pair20 => y2 * y0
  | .together => y0 * y1 * y2


def triangleFKTerminalPartition (y0 y1 y2 : Real) : Real :=
  ∑ c, triangleFKTerminalWeight y0 y1 y2 c


def starFKTerminalPartition (q y0 y1 y2 : Real) : Real :=
  ∑ c, starFKTerminalWeight q y0 y1 y2 c


noncomputable def triangleFKTerminalProbability (y0 y1 y2 : Real)
    (c : ThreeTerminalConnectivity) : Real :=
  triangleFKTerminalWeight y0 y1 y2 c /
    triangleFKTerminalPartition y0 y1 y2


noncomputable def starFKTerminalProbability (q y0 y1 y2 : Real)
    (c : ThreeTerminalConnectivity) : Real :=
  starFKTerminalWeight q y0 y1 y2 c /
    starFKTerminalPartition q y0 y1 y2

end PeriodicPlanar
end FK
end StatMech
