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
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedStripWindow.Part6


namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

open StatMech.Onsager

noncomputable section

def hexCSSourceBelow (R : ℕ) : List (Fin 4) :=
  List.replicate (2 * R) 0 ++
    List.replicate R 1 ++ List.replicate R 2

def hexCSSourceAbove (R : ℕ) : List (Fin 4) :=
  List.replicate (2 * R) 0 ++
    List.replicate R 3 ++ List.replicate R 2

def hexCSEastTail (R : ℕ) (dx : ℤ) : List (Fin 4) :=
  List.replicate ((R : ℤ) + 1 - dx).toNat 0

def hexCSWestNorthEastTail (R : ℕ) (dx dy : ℤ) : List (Fin 4) :=
  List.replicate (dx + (R : ℤ)).toNat 2 ++
    List.replicate ((R : ℤ) - dy).toNat 1 ++
    List.replicate (2 * R + 1) 0

def hexCSSouthEastTail (R : ℕ) (dx dy : ℤ) : List (Fin 4) :=
  List.replicate (dy + R).toNat 3 ++
    List.replicate ((R : ℤ) + 1 - dx).toNat 0

end
end StatMech.Universality
