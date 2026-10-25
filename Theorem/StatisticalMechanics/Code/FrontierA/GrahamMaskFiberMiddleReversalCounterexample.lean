/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamMaskFiberMiddleReversalCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversal.Part24
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamThreeGateBoundaryCounterexample.Part2
import Def.StatisticalMechanics.Code.FrontierA.GrahamMaskFiberMiddleReversalCounterexample
open Finset


namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent


theorem canonicalGateCounterColoring_leftSourcePattern :
    LeftSourcePattern canonicalGateCounterEnds canonicalGateCounterSupport
      {0, 1} {1, 2} canonicalGateCounterColoring := by
  have hc := colorClasses_coloringOfRowData
    (m := canonicalGateCounterSupport) (K := canonicalGateCounterK)
    (P := canonicalGateCounterC0) (Q := canonicalGateCounterC2)
    (by decide) (by decide) (by decide)
  rw [LeftSourcePattern]
  simp only [canonicalGateCounterColoring]
  rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  exact canonicalGateCounter_cell_sources


end StatMech.GrahamGHS.FourColor
