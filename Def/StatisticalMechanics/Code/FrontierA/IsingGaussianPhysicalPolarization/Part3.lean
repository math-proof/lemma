/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalPolarization.Part2
open Filter Finset Polynomial Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteIsingWeightedCumulantLinePolynomial
    (beta : Real) (positive direction : V -> Real) (order : Nat) : Real[X] :=
  scalarCumulantLinePolynomial
    (finiteIsingWeightedRawMomentLinePolynomial G beta positive direction) order

end
end StatMech.FrontierA
