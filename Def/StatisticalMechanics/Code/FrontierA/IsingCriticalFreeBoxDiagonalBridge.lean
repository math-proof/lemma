/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalFreeBoxDiagonalBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalFreeBoxLocalObservables.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusGrowingSupport
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCompactSupportScaling
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNonnegativeNewman
open Filter Finset MeasureTheory Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}

def freeBoxGrowingRowOrderFamily (n : Nat) : Finset (Nat × Nat) :=
  {n} ×ˢ Finset.range (n + 1)

noncomputable def finiteSupportBoxRadius (A : Finset (Site d)) : Nat :=
  Classical.choose (finite_subset_box (↑A : Set (Site d)) A.finite_toSet)

end
end StatMech.FrontierA
