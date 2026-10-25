/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorInvariantComponentCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorInvariantComponentSelector
open Finset
open Classical
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

def parallelCounterEnds : Fin 6 -> Sym2 (Fin 4)
  | 0 => s(1, 2)
  | 1 => s(1, 2)
  | 2 => s(2, 3)
  | 3 => s(1, 2)
  | 4 => s(0, 1)
  | 5 => s(2, 3)

def parallelCounterColor : Fin 6 -> Fin 4
  | 0 => 3
  | 1 => 3
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 1

def parallelCounterColorU :
    ↑(Finset.univ : Finset (Fin 6)) -> Fin 4 :=
  fun i => parallelCounterColor i.1

end StatMech.GrahamGHS.FourColor
