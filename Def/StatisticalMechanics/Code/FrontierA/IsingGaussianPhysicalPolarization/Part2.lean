/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalPolarization
open Filter Finset Polynomial Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def scalarCumulantLinePolynomial (moments : Nat -> Real[X]) : Nat -> Real[X]
  | 0 => 0
  | n + 1 => moments (n + 1) -
      ∑ k : Fin n, C (n.choose k : Real) *
        scalarCumulantLinePolynomial moments (k + 1) * moments (n - k)
termination_by order => order
decreasing_by omega

end
end StatMech.FrontierA
