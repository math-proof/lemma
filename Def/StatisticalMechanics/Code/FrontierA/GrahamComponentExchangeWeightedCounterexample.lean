/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamComponentExchangeWeightedCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamComponentExchangeUnitPacking.Part2
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent


def weightedCollisionEnds : Fin 4 → Sym2 (Fin 4)
  | 0 => s(0, 1)
  | 1 => s(0, 1)
  | 2 => s(0, 1)
  | 3 => s(0, 2)

end StatMech.GrahamGHS.FourColor
