/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc51armforest.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Walls.bc38acyclic.Part6
import Theorem.StatisticalMechanics.Code.Walls.bc39spanning.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc50arminjection.Part2
import Def.StatisticalMechanics.Code.Walls.bc51armforest.Part2
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal

open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc51_armForestEmbedding_iff_globalArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    bc51_ArmForestEmbedding ω n ↔ bc51_GlobalArmForest ω n :=
  Iff.rfl


theorem bc51_armForestReaching_of_armEmbedding (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : bc51_ArmForestEmbedding ω n) : sfa_ArmForestReaching ω n :=
  bc51_armForestReaching_of_globalArmForest ω n
    ((bc51_armForestEmbedding_iff_globalArmForest ω n).mp h)


theorem bc51_openSubgraph_removeSite_le (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    openSubgraph d (removeSite x ω) ≤ openSubgraph d ω := by
  intro u v h
  obtain ⟨hlat, hopen⟩ := h
  refine ⟨hlat, ?_⟩
  by_cases hx : x ∈ (s(u, v) : Sym2 (Site d))
  · rw [removeSite_apply_of_mem hx] at hopen; exact absurd hopen (by simp)
  · rwa [removeSite_apply_of_notMem hx] at hopen


theorem bc51_cutWalk_lift {x a b : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (w : (openSubgraph d (removeSite x ω)).Walk a b) (hwx : x ∉ w.support) :
    ∃ w' : (openSubgraph d ω).Walk a b, x ∉ w'.support ∧
      (∀ e, e ∈ w'.edges → e ∈ (openSubgraph d ω).edgeSet) := by
  classical
  refine ⟨w.mapLe (bc51_openSubgraph_removeSite_le x ω), ?_, ?_⟩
  · rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hwx
  · intro e he; exact (w.mapLe (bc51_openSubgraph_removeSite_le x ω)).edges_subset_edgeSet he


theorem bc51_walk_transfer_to_T {a b x : Site d} {ω : ConfigSpace (Sym2 (Site d))}
    (T : SimpleGraph (Site d)) (w' : (openSubgraph d ω).Walk a b) (hwx : x ∉ w'.support)
    (hcov : ∀ e, e ∈ w'.edges → e ∈ T.edgeSet) :
    ∃ w : T.Walk a b, x ∉ w.support := by
  refine ⟨w'.transfer T hcov, ?_⟩
  rw [SimpleGraph.Walk.support_transfer]; exact hwx


open Classical in


theorem bc51_globalArmForest_of_forestCover (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (Vall : Finset (Site d)) (T : SimpleGraph (Site d)) (hTdec : DecidableRel T.Adj)
    (B : Set (Site d)) (c : Site d → Fin 3 → Site d) (zr : Site d → Fin 3 → Site d)
    (hTac : T.IsAcyclic)
    (hTopen : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    (hTsupp : ∀ u v, T.Adj u v → u ∈ Vall)
    (hBbd : B ⊆ vertexBoundary d n)
    (hsurv : (∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) ∨ (∃ v, spc_OnBPath T B v))
    (hData : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      (∀ i, T.Adj x (c x i)) ∧
      (¬ Connected d (removeSite x ω) (c x 0) (c x 1) ∧
       ¬ Connected d (removeSite x ω) (c x 0) (c x 2) ∧
       ¬ Connected d (removeSite x ω) (c x 1) (c x 2)) ∧
      (∀ i, zr x i ∈ B ∧ ∃ w : (openSubgraph d (removeSite x ω)).Walk (c x i) (zr x i),
        x ∉ w.support ∧
        (∀ e, e ∈ (w.mapLe (bc51_openSubgraph_removeSite_le x ω)).edges → e ∈ T.edgeSet))) :
    bc51_GlobalArmForest ω n := by
  classical
  refine ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hsurv, ?_⟩
  intro x hxbox htri
  obtain ⟨hadj, hcut, hreach⟩ := hData x hxbox htri
  refine ⟨hadj, hcut, ?_⟩
  intro i
  obtain ⟨hzr, w, hwx, hcov⟩ := hreach i
  refine ⟨hzr, ?_⟩
  
  obtain ⟨w', hw'x, _⟩ := bc51_cutWalk_lift w hwx
  
  exact bc51_walk_transfer_to_T T (w.mapLe (bc51_openSubgraph_removeSite_le x ω))
    (by rw [SimpleGraph.Walk.support_mapLe_eq_support]; exact hwx) hcov


theorem bc51_arc_perArm_reaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hres : arc_TrifArmsRemoveSiteInfinite ω n)
    (x : Site d) (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x) :
    ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
      (∀ i, (openSubgraph d ω).Adj x (c i)) ∧
      (∀ i, c i ≠ x) ∧
      (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
       ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
       ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
      (∀ i, zr i ∈ vertexBoundary d (n + 1) ∧
        ∃ w : (openSubgraph d (removeSite x ω)).Walk (c i) (zr i), x ∉ w.support) :=
  arc_trif_arm_data ω n hres x hxbox htri

open Classical in


theorem bc51_globalArmForest_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (a i))
    (habdry : ∀ i, a i ∈ vertexBoundary d n)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    (hsep : ¬ Connected d (removeSite x ω) (a 0) (a 1) ∧
            ¬ Connected d (removeSite x ω) (a 0) (a 2) ∧
            ¬ Connected d (removeSite x ω) (a 1) (a 2)) :
    bc51_GlobalArmForest ω n := by
  classical
  
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, _hRne, hData⟩ :=
    sfa_armForestReaching_star ω n a hsingle hadj habdry hxne hainj hsep
  exact ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd,
    Or.inl ⟨x, hxbox, htri⟩, hData⟩

open Classical in


theorem bc51_globalArmForest_of_boundary_edge (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {b₁ b₂ : Site d} (hb1 : b₁ ∈ vertexBoundary d n) (hb2 : b₂ ∈ vertexBoundary d n)
    (hbne : b₁ ≠ b₂) (hopen : (openSubgraph d ω).Adj b₁ b₂)
    (hnotrif : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    bc51_GlobalArmForest ω n := by
  classical
  obtain ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, hRne, hData⟩ :=
    sfa_armForestReaching_of_boundary_edge ω n hb1 hb2 hbne hopen hnotrif
  exact ⟨Vall, T, hTdec, B, c, zr, hTac, hTopen, hTsupp, hBbd, Or.inr hRne, hData⟩


end StatMech.Walls
