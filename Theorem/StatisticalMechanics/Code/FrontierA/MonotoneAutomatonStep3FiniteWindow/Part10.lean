/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part9
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem measurableSet_step3ContactEvent (T : MonotoneAutomaton d)
    (D : ℕ) (p : Site d × Site d) :
    MeasurableSet (step3ContactEvent T D p) := by
  by_cases hdist : l1dist d p.1 p.2 = D
  · have heq : step3ContactEvent T D p =
        {q | p.1 ∈ pairLowInfiniteVertices (interpolatedHighPair T q)} ∩
          {q | p.2 ∈ pairNearestHighSet (interpolatedHighPair T q) 0} := by
      ext q
      simp [step3ContactEvent, hdist]
    rw [heq]
    exact ((measurable_interpolatedHighPair T)
      (measurableSet_pairLowInfinite p.1)).inter
        ((measurable_interpolatedHighPair T)
          (measurableSet_pairNearestHighSet 0 p.2))
  · have hempty : step3ContactEvent T D p = ∅ := by
      ext q
      simp [step3ContactEvent, hdist]
    rw [hempty]
    exact MeasurableSet.empty

end StatMech.FrontierA
