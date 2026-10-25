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
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalObservables.Part2
open Filter Finset MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB StatMech.Probability

noncomputable section

variable {d : Nat}


theorem criticalTorusCompactWeightedMoment_tendsto
    (hd : 2 < d) (A : Finset (Site d)) (a : Site d → Real) (order : Nat) :
    Tendsto
      (fun n ↦ criticalTorusLocalObservableExpectation A
        (fun sigma ↦ compactWeightedSpin A a sigma ^ order) n)
      atTop
      (nhds (criticalFreeLocalObservableExpectation A
        (fun sigma ↦ compactWeightedSpin A a sigma ^ order))) :=
  criticalTorusLocalObservableExpectation_tendsto hd A _


end
end StatMech.FrontierA
