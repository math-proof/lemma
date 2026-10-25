/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedDomainActive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomain.Part5
open Finset Set SimpleGraph


namespace StatMech.FK

noncomputable section

variable {Vin Vout : Type*} [Fintype Vin] [Fintype Vout]

variable [DecidableEq Vin] [DecidableEq Vout]

variable (Gin : SimpleGraph Vin) [DecidableRel Gin.Adj]

variable (Gout : SimpleGraph Vout) [DecidableRel Gout.Adj]

variable (iota : Vin -> Vout)


def ocd_innerRestrictActive
    (hadjm : ocd_AdjMatch Gin Gout iota)
    (rho : ConfigSpace Gout.edgeSet) : ConfigSpace Gin.edgeSet :=
  fun e => rho ⟨ocd_innerEdge iota e.1, by
    have he : e.1 ∈ Gin.edgeSet := e.2
    rw [← e.1.out_eq] at he ⊢
    rw [ocd_innerEdge_mk, SimpleGraph.mem_edgeSet, ← hadjm]
    simpa only [SimpleGraph.mem_edgeSet] using he⟩

end
end StatMech.FK
