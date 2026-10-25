/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedLeeYang.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part15
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedLeeYang
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def finiteIsingWeightedFieldPartition
    (beta : Real) (a : V -> Real) (z : Complex) : Complex :=
  ∑ s : ConfigSpace V, (zeroFieldInteractionWeight G beta s : Complex) *
    Complex.exp (z * ∑ v : V, (a v : Complex) * spin s v)

end
end StatMech.FrontierA
