/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalCubeInfrared
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation.Part3
open Filter Finset Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


section CriticalFiniteBox

def criticalFiniteBoxRowSusceptibility (d n : Nat)
    (y : sctBox d n) : Real :=
  ∑ x : sctBox d n, criticalFiniteBoxPairCorrelation d n x y


end CriticalFiniteBox
end
end StatMech.FrontierA
