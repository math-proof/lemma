/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalPolarization.Part3
open Filter Finset Polynomial Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


namespace PhysicalIsing

noncomputable def criticalFiniteBoxWeightedScaledCumulantLinePolynomial
    (d n : Nat) (hd : 2 <= d)
    (positive direction : sctBox d n -> Real) (order : Nat) : Real[X] :=
  C (criticalFiniteBoxWeightedFourthScale d n hd ^ order) *
    finiteIsingWeightedCumulantLinePolynomial
      (sctBoxGraph d n) (IsingFK.betaC (magnetization d))
        positive direction order

end PhysicalIsing
end
end StatMech.FrontierA
