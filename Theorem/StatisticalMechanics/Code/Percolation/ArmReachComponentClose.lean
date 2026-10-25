/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/ArmReachComponentClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem arc_x_isolated (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) (y : Site d) :
    ¬ (openSubgraph d (removeSite x ω)).Adj x y := by
  intro hadj
  obtain ⟨_, hopen⟩ := hadj
  rw [removeSite_apply_of_mem (by simp)] at hopen
  exact Bool.false_ne_true hopen


theorem arc_walk_avoids_x {x a b : Site d} {ω : ConfigSpace (Sym2 (Site d))} (hax : a ≠ x)
    (w : (openSubgraph d (removeSite x ω)).Walk a b) : x ∉ w.support := by
  induction w with
  | nil => simpa using (Ne.symm hax)
  | @cons u v c huv w' ih =>
    rw [Walk.support_cons, List.mem_cons, not_or]
    refine ⟨Ne.symm hax, ?_⟩
    have hvx : v ≠ x := fun h => by subst h; exact arc_x_isolated v ω u huv.symm
    exact ih hvx


theorem arc_infinite_cluster_reaches_boundary
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n) (x a : Site d)
    (hax : a ≠ x) (habox : a ∈ box d n)
    (hinf : (cluster d (removeSite x ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d n,
      ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, x ∉ w.support := by
  classical
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff (removeSite x ω) a).mp hinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨b, c, hbc, hb, hc, hr⟩ :=
    tfc_walk_crossing (openSubgraph d (removeSite x ω)) (fun v => v ∈ box d n) w habox hybox
  have hblat : (hypercubicLattice d).Adj b c := (openSubgraph_le (removeSite x ω)) hbc
  refine ⟨b, tfc_boundary_cross_vertex n hn b c hb hc hblat, ?_⟩
  obtain ⟨wab⟩ := hr
  exact ⟨wab, arc_walk_avoids_x hax wab⟩


theorem arc_connected_removeSite_reaches_boundary
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n) (x a : Site d)
    (hax : a ≠ x) (habox : a ∈ box d n)
    (hinf : (cluster d (removeSite x ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d n, Connected d (removeSite x ω) a z := by
  obtain ⟨z, hzb, w, _⟩ := arc_infinite_cluster_reaches_boundary ω n hn x a hax habox hinf
  exact ⟨z, hzb, ⟨w⟩⟩


end Percolation
end StatMech
