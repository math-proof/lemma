/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DisjointArmEndsProve.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Def.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part4
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem daep_mem_globalCutArmEnds {T : Finset (Site d)} {ω : ConfigSpace (Sym2 (Site d))}
    {n : ℕ} {a z : Site d} :
    z ∈ daep_globalCutArmEnds T ω n a ↔
      z ∈ vertexBoundary d n ∧ Connected d (removeSites T ω) a z := by
  classical
  rw [daep_globalCutArmEnds, Finset.mem_filter, tfc_mem_boundaryFinset]


theorem daep_globalCutArmEnds_connected (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) {a z : Site d} (hz : z ∈ daep_globalCutArmEnds T ω n a) : Connected d ω a z :=
  connected_mono (daep_removeSites_le T ω) (daep_mem_globalCutArmEnds.mp hz).2


theorem daep_globalCutArmEnds_disjoint_of_disconnected (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {a₁ a₂ : Site d}
    (hdis : ¬ Connected d (removeSites T ω) a₁ a₂) :
    Disjoint (daep_globalCutArmEnds T ω n a₁) (daep_globalCutArmEnds T ω n a₂) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [daep_mem_globalCutArmEnds] at hw1 hw2
  exact hdis (hw1.2.trans hw2.2.symm)


theorem daep_infinite_reaches_boundary (ω' : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (a : Site d) (habox : a ∈ box d n) (hinf : (cluster d ω' a).Infinite) :
    ∃ z ∈ vertexBoundary d n, Connected d ω' a z := by
  classical
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff ω' a).mp hinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨c, e, hce, hc, he, hr⟩ :=
    tfc_walk_crossing (openSubgraph d ω') (fun v => v ∈ box d n) w habox hybox
  have hclat : (hypercubicLattice d).Adj c e := (openSubgraph_le ω') hce
  exact ⟨c, tfc_boundary_cross_vertex n hn c e hc he hclat, hr⟩


theorem daep_globalCutArmEnds_nonempty (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (a : Site d) (habox : a ∈ box d n)
    (hinf : (cluster d (removeSites T ω) a).Infinite) :
    (daep_globalCutArmEnds T ω n a).Nonempty := by
  classical
  obtain ⟨z, hzb, hzc⟩ := daep_infinite_reaches_boundary (removeSites T ω) n hn a habox hinf
  exact ⟨z, daep_mem_globalCutArmEnds.mpr ⟨hzb, hzc⟩⟩


end Percolation
end StatMech
