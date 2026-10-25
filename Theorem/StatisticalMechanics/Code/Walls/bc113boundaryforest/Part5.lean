/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.bc113boundaryforest.Part4
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem bc113_bForest_degree_ge_two_of_child (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B) [DecidableRel (bc113_bForest G B hreach).Adj]
    {v w : V} (hv : ¬ B v) (hadjw : (bc113_bForest G B hreach).Adj v w)
    (hltw : bc113_toB G B v < bc113_toB G B w) :
    2 ≤ (bc113_bForest G B hreach).degree v := by
  classical
  
  have hpar := bc113_bForest_adj_parent G B hreach hv
  have hparlt := (bc113_parent_spec G B hreach hv).2
  set p := bc113_parent G B hreach v with hp
  have hpw : p ≠ w := by
    intro h; rw [h] at hparlt; omega
  
  have hsub : {p, w} ⊆ (bc113_bForest G B hreach).neighborFinset v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rw [SimpleGraph.mem_neighborFinset]
    rcases hz with rfl | rfl
    · exact hpar
    · exact hadjw
  calc 2 = ({p, w} : Finset V).card := by rw [Finset.card_pair hpw]
    _ ≤ ((bc113_bForest G B hreach).neighborFinset v).card := Finset.card_le_card hsub
    _ = (bc113_bForest G B hreach).degree v := SimpleGraph.card_neighborFinset_eq_degree _ _


theorem bc113_bForest_leaves_on_boundary (G : SimpleGraph V) (B : V → Prop)
    (hreach : bc113_ReachesB G B) [DecidableRel (bc113_bForest G B hreach).Adj]
    (hchild : bc113_HasChild G B hreach)
    {v : V} (hdeg : (bc113_bForest G B hreach).degree v = 1) : B v := by
  by_contra hv
  obtain ⟨w, hadjw, hltw⟩ := hchild v hv
  have h2 := bc113_bForest_degree_ge_two_of_child G B hreach hv hadjw hltw
  omega


end StatMech.Walls
