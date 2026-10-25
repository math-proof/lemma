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
open Filter Finset MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB StatMech.Probability

noncomputable section

variable {d : Nat}


def criticalTorusLocalRestriction (A : Finset (Site d)) (n : Nat)
    (sigma : ConfigSpace (IsingDyadicTorus d n)) : ConfigSpace {x // x ∈ A} :=
  fun x ↦ sigma (isingSiteToDyadicTorus n x.1)


def criticalInfiniteLocalRestriction (A : Finset (Site d))
    (omega : ConfigSpace (Site d)) : ConfigSpace {x // x ∈ A} :=
  fun x ↦ omega x.1


def criticalTorusLocalObservableExpectation
    (A : Finset (Site d)) (f : ConfigSpace {x // x ∈ A} → Real)
    (n : Nat) : Real :=
  expJ (isingTorusGraph d n).edgeFinset
    (fun _ ↦ IsingFK.betaC (magnetization d)) (fun _ ↦ 0)
    (fun sigma ↦ f (criticalTorusLocalRestriction A n sigma))


def criticalFreeLocalObservableExpectation
    (A : Finset (Site d)) (f : ConfigSpace {x // x ∈ A} → Real) : Real :=
  ∫ omega, f (criticalInfiniteLocalRestriction A omega)
    ∂(freeState d (IsingFK.betaC (magnetization d)) 0 :
      Measure (ConfigSpace (Site d)))

end
end StatMech.FrontierA
