/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorStrictDescentCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorUniformMaskSelector.Part4
open Finset
open scoped symmDiff


namespace StatMech.GrahamGHS.FourColor

def counterEnds : Fin 7 -> Sym2 (Fin 6)
  | 0 => s(1, 3)
  | 1 => s(0, 2)
  | 2 => s(2, 3)
  | 3 => s(1, 3)
  | 4 => s(2, 3)
  | 5 => s(0, 4)
  | 6 => s(2, 5)

def counterC : Fin 7 -> Fin 4
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 3
  | 4 => 0
  | 5 => 0
  | 6 => 2

def counterCU : ↑(Finset.univ : Finset (Fin 7)) -> Fin 4 :=
  fun i => counterC i.1

def counterD : Fin 7 -> Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 2

def counterDU : ↑(Finset.univ : Finset (Fin 7)) -> Fin 4 :=
  fun i => counterD i.1

end StatMech.GrahamGHS.FourColor
