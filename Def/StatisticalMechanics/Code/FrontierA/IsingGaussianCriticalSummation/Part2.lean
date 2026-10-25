/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianCriticalSummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalCubeInfrared
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianIndependentDisentangling.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalSummation
open Filter Finset Set Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {d : Nat}


section FiniteTree

variable {V : Type*} [Fintype V] [DecidableEq V]


def finiteDistinctIntegratedFourthCumulant
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V → Real) (i : V) : Real :=
  ∑ j : V, ∑ k : V, ∑ l : V,
    if i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l then
      finiteIsingFourthUrsell G beta J i j k l
    else 0

end FiniteTree
end
end StatMech.FrontierA
