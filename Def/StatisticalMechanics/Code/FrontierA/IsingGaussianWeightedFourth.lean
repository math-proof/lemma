/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedFourth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianCriticalNewman.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedFourth
open Filter Finset Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Lattice Percolation Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

def finiteWeightedParityFourthCumulant
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : Real) (J : Sym2 V -> Real) (a : V -> Real) : Real :=
  ∑ i : V, ∑ j : V, ∑ k : V, ∑ l : V,
    a i * a j * a k * a l *
      finiteParityFourthUrsell G beta J i j k l


end
end StatMech.FrontierA
