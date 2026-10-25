/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc42rootward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc40funnel.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc41rootside.Part3
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc42_removeSite_openSubgraph_le (y : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d (removeSite y ω) ≤ openSubgraph d ω := by
  intro x z h
  obtain ⟨hadj, hval⟩ := h
  refine ⟨hadj, ?_⟩
  by_cases hy : y ∈ s(x, z)
  · rw [removeSite_apply_of_mem hy] at hval; exact absurd hval (by simp)
  · rwa [removeSite_apply_of_notMem hy] at hval


theorem bc42_avoidingWalk_of_connected_removeSite (ω : ConfigSpace (Sym2 (Site d))) {x y z : Site d}
    (hxy : x ≠ y) (h : Connected d (removeSite y ω) x z) :
    ∃ p : (openSubgraph d ω).Walk x z, ∀ v ∈ p.support, v ≠ y := by
  obtain ⟨w⟩ := h
  refine ⟨w.mapLe (bc42_removeSite_openSubgraph_le y ω), ?_⟩
  intro v hv
  rw [SimpleGraph.Walk.support_mapLe_eq_support] at hv
  exact fun hvy => (arc_walk_avoids_x hxy w) (hvy ▸ hv)


theorem bc42_avoidingWalk_iff_connected_removeSite (ω : ConfigSpace (Sym2 (Site d)))
    {x y z : Site d} (hxy : x ≠ y) :
    (∃ p : (openSubgraph d ω).Walk x z, ∀ v ∈ p.support, v ≠ y) ↔
      Connected d (removeSite y ω) x z := by
  constructor
  · rintro ⟨p, hp⟩
    have : Connected d (removeSites {y} ω) x z := by
      apply bc39_connected_removeSites_of_walk_avoids {y} ω p
      intro v hv; rw [Finset.mem_singleton]; exact hp v hv
    rwa [daep_removeSites_singleton] at this
  · exact bc42_avoidingWalk_of_connected_removeSite ω hxy


theorem bc42_rootWardAvoidingWalk_allParRank_false_of_farParent
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ y₀ z₀ : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (hy0box : y₀ ∈ box d n) (htriy0 : IsTrifurcation d ω y₀)
    (hne : x₀ ≠ y₀) (hconn : Connected d ω x₀ y₀)
    (hadj : bc37_ArmAdjacent ω n y₀ z₀) (hx0z0 : x₀ ≠ z₀)
    (hfar : ¬ Connected d (removeSite y₀ ω) x₀ z₀) :
    ¬ ∀ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
        bc41_RootWardAvoidingWalk ω n rank par := by
  intro hwalk
  
  set rank : Site d → ℕ ×ₗ ℕ := fun w => toLex (if w = y₀ then 1 else 0, 0) with hrank
  set par : Site d → Site d := fun _ => z₀ with hpar
  have hlt : rank x₀ < rank y₀ := by
    simp only [hrank, if_neg hne, if_pos]
    exact stt_lex_lt_fst (by norm_num)
  
  obtain ⟨p, hp⟩ :=
    hwalk rank par x₀ hx0box htri0 y₀ hy0box htriy0 hne hconn hlt (by simpa [hpar] using hx0z0)
      (by simpa [hpar] using hadj)
  
  have hconn_cut : Connected d (removeSite y₀ ω) x₀ (par y₀) :=
    (bc42_avoidingWalk_iff_connected_removeSite ω hne).mp ⟨p, hp⟩
  simp only [hpar] at hconn_cut
  exact hfar hconn_cut


end StatMech.Walls
