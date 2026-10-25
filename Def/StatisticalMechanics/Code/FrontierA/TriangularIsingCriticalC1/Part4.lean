/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalParameter.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part3
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

def triangularIsingCriticalFirstOuterMajorant
    (m K x : Real) : Real :=
  (K / m) *
    (Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x *
      (∫ y in (-Real.pi)..Real.pi,
        StatMech.Onsager.ons_criticalOneDimMajorant y) + 2 * Real.pi)

end
end StatMech.FrontierA
