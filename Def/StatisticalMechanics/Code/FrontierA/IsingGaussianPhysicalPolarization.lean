/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianPhysicalPolarization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
open Filter Finset Polynomial Topology
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising Sharpness StatMech.FrontierB

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteIsingWeightedRawMomentLinePolynomial
    (beta : Real) (positive direction : V -> Real)
    (order : Nat) : Real[X] :=
  C ((∑ s : ConfigSpace V, zeroFieldInteractionWeight G beta s)⁻¹) *
    ∑ s : ConfigSpace V, C (zeroFieldInteractionWeight G beta s) *
      (C (finiteIsingWeightedSpinReal positive s) +
        X * C (finiteIsingWeightedSpinReal direction s)) ^ order

end
end StatMech.FrontierA
