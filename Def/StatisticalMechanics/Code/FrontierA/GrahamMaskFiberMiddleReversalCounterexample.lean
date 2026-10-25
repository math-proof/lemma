/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversalCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamThreeGateBoundaryCounterexample.Part2
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent


def canonicalGateCounterColoring :
    ↑canonicalGateCounterSupport → Fin 4 :=
  coloringOfRowData canonicalGateCounterSupport canonicalGateCounterK
    canonicalGateCounterC0 canonicalGateCounterC2

end StatMech.GrahamGHS.FourColor
