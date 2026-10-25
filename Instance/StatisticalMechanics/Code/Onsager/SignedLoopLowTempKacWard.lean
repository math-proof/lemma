/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopLowTempKacWard.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopLowTempDual.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardArbitraryValenceClosure
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.Ising StatMech.Lattice

open StatMech.FrontierA

noncomputable section

variable {V E : Type*} [Fintype V] [Fintype E]
  [DecidableEq V] [DecidableEq E]

noncomputable instance kwg_subdivGraph_decidableAdj (ends : E -> Sym2 V) :
    DecidableRel (kwg_subdivGraph ends).Adj := Classical.decRel _

end
end StatMech.Onsager
