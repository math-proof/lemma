/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalPolarization.Part3
open Filter Finset Polynomial Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem finiteIsingWeightedCumulantLinePolynomial_eval
    (beta : Real) (positive direction : V -> Real)
    (order : Nat) (r : Real) :
    (finiteIsingWeightedCumulantLinePolynomial
      G beta positive direction order).eval r =
      PhysicalIsing.finiteIsingWeightedCumulant G beta
        (positive + r • direction) order := by
  unfold finiteIsingWeightedCumulantLinePolynomial
    PhysicalIsing.finiteIsingWeightedCumulant
  rw [scalarCumulantLinePolynomial_eval]
  congr 1
  funext m
  exact finiteIsingWeightedRawMomentLinePolynomial_eval
    G beta positive direction m r

theorem finiteIsingWeightedCumulantLinePolynomial_degree_lt
    (beta : Real) (positive direction : V -> Real) (order : Nat) :
    (finiteIsingWeightedCumulantLinePolynomial
      G beta positive direction order).degree < (order + 1 : Nat) := by
  apply lt_of_le_of_lt (Polynomial.degree_le_of_natDegree_le ?_)
    (by exact_mod_cast Nat.lt_succ_self order)
  exact scalarCumulantLinePolynomial_natDegree_le _
    (finiteIsingWeightedRawMomentLinePolynomial_natDegree_le
      G beta positive direction) order

end
end StatMech.FrontierA
