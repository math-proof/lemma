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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalObservables.Part3
open Filter Finset MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB StatMech.Probability

noncomputable section

variable {d : Nat}


def criticalTorusCompactWeightedCumulant
    (A : Finset (Site d)) (a : Site d → Real) (n order : Nat) : Real :=
  scalarCumulantsOfMoments
    (finiteIsingWeightedRawMoment (isingTorusGraph d n)
      (IsingFK.betaC (magnetization d)) (compactTorusWeight A a n)) order


def criticalFreeCompactWeightedCumulant
    (A : Finset (Site d)) (a : Site d → Real) (order : Nat) : Real :=
  scalarCumulantsOfMoments
    (fun m ↦ criticalFreeLocalObservableExpectation A
      (fun sigma ↦ compactWeightedSpin A a sigma ^ m)) order


end
end StatMech.FrontierA
