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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalFreeBoxLocalObservables
open Filter Finset MeasureTheory Topology
open scoped BigOperators


namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising Lattice Sharpness StatMech.FrontierB
  StatMech.Probability

noncomputable section

variable {d : Nat}

def criticalFreeBoxLocalObservableExpectation
    (A : Finset (Site d)) (f : ConfigSpace {x // x ∈ A} → Real)
    (n : Nat) : Real :=
  ∫ omega, f (criticalInfiniteLocalRestriction A omega)
    ∂(freeMeasure d n (IsingFK.betaC (magnetization d)) 0 :
      Measure (ConfigSpace (Site d)))

end
end StatMech.FrontierA
