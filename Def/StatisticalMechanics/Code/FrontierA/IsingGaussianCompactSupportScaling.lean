/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCompactSupportScaling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalObservables.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusCumulants.Part2
open Filter Finset MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


def criticalTorusCompactScaledField
    (A : Finset (Site d)) (a : Site d → Real) (c : Nat → Real)
    (n : Nat) (sigma : ConfigSpace (IsingDyadicTorus d n)) : Real :=
  c n * isingTorusSmearedSpin (compactTorusWeight A a n) sigma


def criticalTorusCompactScaledFieldLaw
    (A : Finset (Site d)) (a : Site d → Real) (c : Nat → Real)
    (n : Nat) : ProbabilityMeasure Real :=
  isingTorusFieldLaw d n (IsingFK.betaC (magnetization d))
    (criticalTorusCompactScaledField A a c n)

end
end StatMech.FrontierA
