/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExteriorPeriod.Part2


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

def hexCSBoundarySource {T L : ℕ}
    (R : ℕ) (e : HexCSIncidence T L) : List (Fin 4) :=
  match e.vtx.1.color, e.edge with
  | .black, 0 =>
      if 0 ≤ hexAWTrans e.vtx.1 then hexCSSourceBelow R
      else hexCSSourceAbove R
  | .white, 0 => hexCSSourceBelow R
  | .white, 1 => hexCSSourceBelow R
  | .white, 2 => hexCSSourceAbove R
  | _, _ => []


def hexCSBoundaryTail {T L : ℕ}
    (R : ℕ) (e : HexCSIncidence T L) : List (Fin 4) :=
  let dx := (hexCSOutsideRel e).1
  let dy := (hexCSOutsideRel e).2
  match e.vtx.1.color, e.edge with
  | .black, 0 => hexCSEastTail R dx
  | .white, 0 => hexCSWestNorthEastTail R dx dy
  | .white, 1 => hexCSEastTail R dx
  | .white, 2 => hexCSSouthEastTail R dx dy
  | _, _ => []

noncomputable def hexCSBoundaryPeriod {T L : ℕ}
    (R : ℕ) (e : HexCSIncidence T L) (ts : List ℤ) : List (Fin 4) :=
  hexCSBoundarySource R e ++ hexCSBrickDirections 1 ts ++
    hexCSBoundaryTail R e

end
end StatMech.Universality
