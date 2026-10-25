/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExit
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointLocalGeometry.Part8
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part2


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

def hexCSEdgeOfHeading (c : HexAWCoord) (h : Fin 6) : Fin 3 :=
  match c.color, h.val with
  | .black, 4 => 0
  | .black, 0 => 1
  | .black, 2 => 2
  | .white, 1 => 0
  | .white, 3 => 1
  | .white, 5 => 2
  | _, _ => 0


def HexCSHeadingFits (c : HexAWCoord) (h : Fin 6) : Prop :=
  match c.color with
  | .black => h.val % 2 = 0
  | .white => h.val % 2 = 1

end
end StatMech.Universality
