/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingCriticalC1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingIntegralAnalytic.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalParameter.Part2
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingCriticalC1.Part4
open Filter MeasureTheory Topology
open scoped Real Interval


namespace StatMech.FrontierA

noncomputable section

theorem triangularIsingCriticalFirstOuterMajorant_intervalIntegrable
    {m K : Real} :
    IntervalIntegrable (triangularIsingCriticalFirstOuterMajorant m K)
      volume (-Real.pi) Real.pi := by
  let Q : Real := ∫ y in (-Real.pi)..Real.pi,
    StatMech.Onsager.ons_criticalOneDimMajorant y
  have hterm : IntervalIntegrable
      (fun x => Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x * Q)
      volume (-Real.pi) Real.pi := by
    convert StatMech.Onsager.ons_criticalOneDimMajorant_intervalIntegrable.const_mul
      (Real.pi * Q) using 1
    ext x
    ring
  unfold triangularIsingCriticalFirstOuterMajorant
  change IntervalIntegrable
    (fun x => (K / m) *
      (Real.pi * StatMech.Onsager.ons_criticalOneDimMajorant x * Q +
        2 * Real.pi)) volume (-Real.pi) Real.pi
  exact (hterm.add intervalIntegral.intervalIntegrable_const).const_mul (K / m)

end
end StatMech.FrontierA
