module
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianConePolarization.Part4
public import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part15
open scoped BigOperators
open Finset


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianWeightedLeeYang.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierA

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def leeYangWeightedDiagonal (a : V -> Real) (z : Complex) :
    LeeYangVar G -> Complex
  | Sum.inl v => Complex.exp (-2 * (a v : Complex) * z)
  | Sum.inr _ => 0

end
end StatMech.FrontierA
