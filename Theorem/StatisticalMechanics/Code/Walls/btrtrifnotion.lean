/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/btrtrifnotion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bfkforestbuild
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


theorem btr_removed_isolated {T : Finset (Site d)} {ω : ConfigSpace (Sym2 (Site d))} {a b : Site d}
    (ha : a ∈ T) (hconn : Connected d (removeSites T ω) a b) : b = a := by
  obtain ⟨w⟩ := hconn
  cases w with
  | nil => rfl
  | cons hadj w' =>
      exfalso
      rw [openSubgraph_adj] at hadj
      obtain ⟨_, hopen⟩ := hadj
      unfold removeSites at hopen
      rw [if_pos ⟨a, ha, Sym2.mem_mk_left a _⟩] at hopen
      exact Bool.false_ne_true hopen


theorem btr_arm_outside_box {T : Finset (Site d)} {ω : ConfigSpace (Sym2 (Site d))} {a : Site d}
    (hinf : (cluster d (removeSites T ω) a).Infinite) : a ∉ T := by
  intro ha
  have hsub : cluster d (removeSites T ω) a ⊆ {a} := by
    intro b hb
    rw [mem_cluster] at hb
    rw [Set.mem_singleton_iff]
    exact btr_removed_isolated ha hb
  exact hinf (Set.Finite.subset (Set.finite_singleton a) hsub)


end StatMech.Walls
