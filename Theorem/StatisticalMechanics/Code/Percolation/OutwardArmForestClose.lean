/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OutwardArmForestClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafDisjointClose.Part2
import Def.StatisticalMechanics.Code.Percolation.OutwardArmForestClose
open Set SimpleGraph Finset
open scoped BigOperators

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem oaf_openSubgraph_removeSite (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    openSubgraph d (removeSite x ω) = oaf_cutGraph (openSubgraph d ω) x := by
  ext a b
  simp only [openSubgraph_adj, oaf_cutGraph]
  constructor
  · rintro ⟨hadj, hopen⟩
    have hxnotin : x ∉ s(a, b) := by
      intro hx
      rw [removeSite_apply_of_mem hx] at hopen
      exact Bool.false_ne_true hopen
    rw [removeSite_apply_of_notMem hxnotin] at hopen
    refine ⟨⟨hadj, hopen⟩, ?_, ?_⟩
    · rintro rfl; exact hxnotin (Sym2.mem_mk_left a b)
    · rintro rfl; exact hxnotin (Sym2.mem_mk_right a b)
  · rintro ⟨⟨hadj, hopen⟩, hax, hbx⟩
    have hxnotin : x ∉ s(a, b) := by
      rw [Sym2.mem_iff]
      rintro (h | h)
      · exact hax h.symm
      · exact hbx h.symm
    exact ⟨hadj, by rw [removeSite_apply_of_notMem hxnotin]; exact hopen⟩


theorem oaf_connected_removeSite_iff (ω : ConfigSpace (Sym2 (Site d))) (x a b : Site d) :
    Lattice.Connected d (removeSite x ω) a b ↔
      (oaf_cutGraph (openSubgraph d ω) x).Reachable a b := by
  unfold Lattice.Connected
  rw [oaf_openSubgraph_removeSite]


theorem oaf_outwardArm_false_of_rootCover (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {r : Site d} {c : Fin 3 → Site d}
    (hrbox : r ∈ box d n) (htri_r : IsTrifurcation d ω r)
    (hcT : ∀ i, c i ∈ tfc_trifFinset ω n)
    (hcne : ∀ i, c i ≠ r)
    (hcover : ∀ a, Connected d ω r a → a ≠ r →
        ∃ i, Connected d (removeSite r ω) a (c i)) :
    ¬ fld_OutwardArm ω n := by
  intro h
  obtain ⟨a, ⟨_habox, hra, hainf⟩, hpriv, _hfar⟩ := h r hrbox htri_r
  
  have haT : a ∉ tfc_trifFinset ω n := stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω hainf
  
  have hane : a ≠ r := by
    intro he; exact haT (he ▸ tfc_mem_trifFinset.mpr ⟨hrbox, htri_r⟩)
  
  obtain ⟨i, hai⟩ := hcover a hra hane
  exact hpriv (c i) (hcT i) (hcne i) hai


end Percolation
end StatMech
