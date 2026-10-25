/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxLocalObservables.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalObservables.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.ScalarCumulantsContinuity
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalFreeBoxLocalObservables.Part2
open Filter Finset MeasureTheory Topology
open scoped BigOperators


namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising Lattice Sharpness StatMech.FrontierB
  StatMech.Probability

noncomputable section

variable {d : Nat}

def criticalFreeBoxCompactWeightedMoment
    (A : Finset (Site d)) (a : Site d → Real) (n order : Nat) : Real :=
  criticalFreeBoxLocalObservableExpectation A
    (fun sigma ↦ compactWeightedSpin A a sigma ^ order) n


def criticalFreeBoxCompactWeightedCumulant
    (A : Finset (Site d)) (a : Site d → Real) (n order : Nat) : Real :=
  scalarCumulantsOfMoments
    (fun m ↦ criticalFreeBoxCompactWeightedMoment A a n m) order


def compactFreeBoxWeight
    (A : Finset (Site d)) (a : Site d → Real) (n : Nat)
    (x : sctBox d n) : Real :=
  if x.1 ∈ A then a x.1 else 0

end
end StatMech.FrontierA
