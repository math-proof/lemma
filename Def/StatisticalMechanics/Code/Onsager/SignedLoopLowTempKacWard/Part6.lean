/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceClosure
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempKacWard.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

open StatMech.FrontierA

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

def kwg_pathEdgeSign (P : PlanarZ2Subgraph) {u v : P.V}
    (path : P.G.Walk u v) (e : kwg_Edge P) : ℂ :=
  (-1 : ℂ) ^ (kwg_pathEdgeIndices P path).countP
    (fun a => decide (a = e))

end
end StatMech.Onsager
