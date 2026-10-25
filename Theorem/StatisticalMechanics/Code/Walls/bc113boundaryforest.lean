/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem bc113_exists_closer_neighbour (G : SimpleGraph V) {v b : V}
    (hr : G.Reachable v b) (hne : v ≠ b) :
    ∃ u, G.Adj v u ∧ G.dist u b < G.dist v b := by
  
  
  obtain ⟨p, hp⟩ := hr.symm.exists_walk_length_eq_dist
  have hpvb : p.length = G.dist v b := by rw [hp, @SimpleGraph.dist_comm _ G b v]
  have hdvpos : 0 < G.dist v b := by
    apply Nat.pos_of_ne_zero
    rw [SimpleGraph.dist_ne_zero_iff_ne_and_reachable]
    exact ⟨hne, hr⟩
  have hpnn : ¬ p.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length, hpvb]; omega
  refine ⟨p.penultimate, (p.adj_penultimate hpnn).symm, ?_⟩
  have hdl : G.dist b p.penultimate ≤ p.dropLast.length := SimpleGraph.dist_le p.dropLast
  rw [SimpleGraph.Walk.length_dropLast, hpvb, @SimpleGraph.dist_comm _ G b p.penultimate] at hdl
  omega


end StatMech.Walls
