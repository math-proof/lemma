module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalLimit.Part2
public import Theorem.StatisticalMechanics.Code.Probability.KKLfromHC.Part5
public import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivative
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalTorusLocalObservables.Part2
open Filter Finset MeasureTheory Set Topology
open scoped BigOperators


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalTorusLocalObservables.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech Ising Lattice Sharpness StatMech.FrontierB StatMech.Probability

noncomputable section

variable {d : Nat}


def compactTorusWeight (A : Finset (Site d)) (a : Site d → Real) (n : Nat)
    (z : IsingDyadicTorus d n) : Real :=
  ∑ x : {x // x ∈ A},
    if isingSiteToDyadicTorus n x.1 = z then a x.1 else 0

end
end StatMech.FrontierA
