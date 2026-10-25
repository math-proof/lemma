/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamThreeGateBoundaryCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent


def threeGateCounterEnds : Fin 15 -> Sym2 (Fin 6)
  | 0 => s(0, 1)
  | 1 => s(0, 2)
  | 2 => s(0, 3)
  | 3 => s(0, 4)
  | 4 => s(0, 5)
  | 5 => s(1, 2)
  | 6 => s(1, 3)
  | 7 => s(1, 4)
  | 8 => s(1, 5)
  | 9 => s(2, 3)
  | 10 => s(2, 4)
  | 11 => s(2, 5)
  | 12 => s(3, 4)
  | 13 => s(3, 5)
  | 14 => s(4, 5)

def threeGateCounterSupport : Finset (Fin 15) :=
  {0, 1, 4, 5, 7, 8, 9, 10, 11, 12, 14}

def threeGateCounterK : Finset (Fin 15) := {0, 9, 11, 12, 14}

def threeGateCounterS : Finset (Fin 15) := {4, 8, 9, 10, 12}

def threeGateCounterN : Finset (Fin 15) := {1, 9, 11, 12, 14}

def threeGateCounterA : Finset (Fin 15) := {0, 1, 4, 8, 9, 10, 12}


def ThreeGateCounterGated (E : Finset (Fin 15)) : Prop :=
  ¬ connK threeGateCounterEnds E 1 3 ∧
    ¬ connK threeGateCounterEnds (threeGateCounterSupport \ E) 1 3

end StatMech.GrahamGHS.FourColor
