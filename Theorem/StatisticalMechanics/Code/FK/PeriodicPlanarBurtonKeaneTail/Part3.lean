/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTail.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Mathlib.Combinatorics.SimpleGraph.Ends.Properties
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTail
open Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

variable {V : Type} [Countable V] [DecidableEq V]

theorem PeriodicGraph.infiniteCluster_has_open_exit
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x : V)
    (hinf : (P.cluster omega x).Infinite) (K : Finset V) (hxK : x ∈ K) :
    Nonempty (P.InfiniteTailData omega K x) := by
  obtain ⟨D, hD⟩ := P.infiniteCluster_component_after_finset omega x hinf K
  have hcut : (P.tailClusterCut omega x K).Nonempty := by
    refine ⟨⟨x, P.self_mem_cluster omega x⟩, ?_⟩
    simp [PeriodicGraph.tailClusterCut, hxK]
  obtain ⟨⟨v, u⟩, hvD, huCut, hadj⟩ :=
    D.exists_adj_boundary_pair (P.tailClusterGraphPreconnected omega x).out hcut
  have huK : u.1 ∈ K := by simpa [PeriodicGraph.tailClusterCut] using huCut
  have hvK : v.1 ∉ K := by
    intro hv
    exact D.notMem_of_mem hvD (by simp [PeriodicGraph.tailClusterCut, hv])
  exact ⟨{
    inside := u.1
    outside := v.1
    tail := P.tailComponentVertices omega x K D
    inside_mem := huK
    outside_not_mem := hvK
    exit_open := hadj.symm
    outside_mem_tail := ⟨v, hvD, rfl⟩
    tail_infinite := P.tailComponentVertices_infinite omega x K D hD
    tail_subset_cluster := P.tailComponentVertices_subset_cluster omega x K D
    tail_connected_outside :=
      P.tailComponentVertices_connected_outside omega x K D }⟩

end StatMech.FK.PeriodicPlanar
