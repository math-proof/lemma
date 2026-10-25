/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivativeLower.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivative
open scoped BigOperators
open Finset Filter Topology


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]


def ginibreChainEdge {N : Nat} (v : Nat -> V) (j : Fin N) : Sym2 V :=
  s(v j.val, v (j.val + 1))


end
end StatMech.Ising
