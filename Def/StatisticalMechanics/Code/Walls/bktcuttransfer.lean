/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bktcuttransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bkfforest.Part2
import Theorem.StatisticalMechanics.Code.Walls.bktcuttransfer
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


noncomputable def bkt_ctrMap (L : ℕ) (y : Site d) : Site d → Option (Site d) := by
  classical
  exact fun x => if x ∈ bc61_boxAround d L y then none else some x


noncomputable def bkt_ctrGraph (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    SimpleGraph (Option (Site d)) where
  Adj u v :=
    match u, v with
    | some a, some b =>
        a ∉ bc61_boxAround d L y ∧ b ∉ bc61_boxAround d L y ∧ (openSubgraph d ω).Adj a b
    | none, some a => a ∉ bc61_boxAround d L y ∧ bc67_GnIncident ω L y a
    | some a, none => a ∉ bc61_boxAround d L y ∧ bc67_GnIncident ω L y a
    | none, none => False
  symm := by
    constructor
    rintro u v h
    cases u <;> cases v <;> simp_all [SimpleGraph.adj_comm]
  loopless := by
    refine ⟨fun u h => ?_⟩
    cases u with
    | none => exact h
    | some a => exact (openSubgraph d ω).loopless.irrefl a h.2.2

end StatMech.Walls
