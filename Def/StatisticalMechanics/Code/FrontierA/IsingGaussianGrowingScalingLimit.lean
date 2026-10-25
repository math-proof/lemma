/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianGrowingScalingLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalFreeBoxDiagonalBridge
open Filter Finset MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open ProbabilityTheory StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


def criticalTorusGrowingCanonicalField
    (hd : 2 ≤ d) (A : Nat → Finset (Site d)) (a : Nat → Site d → Real)
    (boxScale torusScale : Nat → Nat) (n : Nat)
    (sigma : ConfigSpace (IsingDyadicTorus d (torusScale n))) : Real :=
  PhysicalIsing.criticalFiniteBoxWeightedFourthScale
      d (boxScale n) hd *
    isingTorusSmearedSpin
      (compactTorusWeight (A n) (a n) (torusScale n)) sigma


def criticalTorusGrowingCanonicalFieldLaw
    (hd : 2 ≤ d) (A : Nat → Finset (Site d)) (a : Nat → Site d → Real)
    (boxScale torusScale : Nat → Nat) (n : Nat) : ProbabilityMeasure Real :=
  isingTorusFieldLaw d (torusScale n)
    (IsingFK.betaC (magnetization d))
    (criticalTorusGrowingCanonicalField hd A a boxScale torusScale n)

end
end StatMech.FrontierA
