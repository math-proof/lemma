/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalLimit.Part2
import Theorem.StatisticalMechanics.Code.Probability.KKLfromHC.Part5
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivative
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalObservables.Part4
open Filter Finset MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB StatMech.Probability

noncomputable section

variable {d : Nat}


theorem criticalTorusCompactWeightedCumulant_tendsto
    (hd : 2 < d) (A : Finset (Site d)) (a : Site d → Real) (order : Nat) :
    Tendsto (fun n ↦ criticalTorusCompactWeightedCumulant A a n order)
      atTop (nhds (criticalFreeCompactWeightedCumulant A a order)) := by
  unfold criticalTorusCompactWeightedCumulant
    criticalFreeCompactWeightedCumulant
  apply scalarCumulantsOfMoments_tendsto_of_moments
  intro m
  simpa only [← criticalTorusCompactWeightedMoment_eq_finiteRawMoment] using
    criticalTorusCompactWeightedMoment_tendsto hd A a m


theorem criticalTorusCompactWeightedCumulant_sub_tendsto_zero
    (hd : 2 < d) (A : Finset (Site d)) (a : Site d → Real) (order : Nat) :
    Tendsto
      (fun n ↦ criticalTorusCompactWeightedCumulant A a n order -
        criticalFreeCompactWeightedCumulant A a order)
      atTop (nhds 0) := by
  have hconst : Tendsto
      (fun _ : Nat ↦ criticalFreeCompactWeightedCumulant A a order) atTop
      (nhds (criticalFreeCompactWeightedCumulant A a order)) :=
    tendsto_const_nhds
  simpa using (criticalTorusCompactWeightedCumulant_tendsto
    hd A a order).sub hconst

end
end StatMech.FrontierA
