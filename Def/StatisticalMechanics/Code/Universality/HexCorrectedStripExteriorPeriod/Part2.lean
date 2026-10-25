/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedStripExteriorPeriod.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part8
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripExteriorPeriod


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

def hexCSOutsideRel {T L : ℕ} (e : HexCSIncidence T L) : ℤ × ℤ :=
  hexBrickPos (hexAWNeighbor e.vtx.1 e.edge) -
    hexBrickPos hexCSOutsideStartCoord


def hexCSExteriorTail {T L : ℕ}
    (R : ℕ) (e : HexCSIncidence T L) : List (Fin 4) :=
  let x := (hexCSOutsideRel e).1
  let y := (hexCSOutsideRel e).2
  match e.vtx.1.color, e.edge with
  | .black, 0 =>
      if 0 ≤ hexAWTrans e.vtx.1 then
        List.replicate ((R : ℤ) - x).toNat 0 ++
          List.replicate ((R : ℤ) - y).toNat 1 ++
          List.replicate (2 * R) 2
      else
        List.replicate ((R : ℤ) - x).toNat 0 ++
          List.replicate ((R : ℤ) + y).toNat 3 ++
          List.replicate (2 * R) 2
  | .white, 0 =>
      List.replicate (x + R).toNat 2
  | .white, 1 =>
      List.replicate ((R : ℤ) - x).toNat 0 ++
        List.replicate ((R : ℤ) - y).toNat 1 ++
        List.replicate (2 * R) 2
  | .white, 2 =>
      List.replicate ((R : ℤ) + y).toNat 3 ++
        List.replicate (x + R).toNat 2
  | _, _ => []


noncomputable def hexCSExteriorPeriod {T L : ℕ}
    (R : ℕ) (e : HexCSIncidence T L) (ts : List ℤ) :
    List (Fin 4) :=
  List.replicate R 2 ++ hexCSBrickDirections 1 ts ++
    hexCSExteriorTail R e

end
end StatMech.Universality
