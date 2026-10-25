/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonicalTrifCount.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ArmReachComponentClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanForestArmsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Def.StatisticalMechanics.Code.Percolation.CanonicalTrifCount
open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem ctc2_cluster_removeSite_subset (x a : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    cluster d (removeSite x ω) a ⊆ cluster d ω a := by
  intro y hy
  rw [mem_cluster] at hy ⊢
  obtain ⟨w⟩ := hy
  
  have hle : openSubgraph d (removeSite x ω) ≤ openSubgraph d ω := by
    intro p q hpq
    obtain ⟨hadj, hopen⟩ := hpq
    refine ⟨hadj, ?_⟩
    by_cases hx : x ∈ s(p, q)
    · rw [removeSite_apply_of_mem hx] at hopen; exact absurd hopen (by simp)
    · rwa [removeSite_apply_of_notMem hx] at hopen
  set f : openSubgraph d (removeSite x ω) →g openSubgraph d ω :=
    { toFun := id, map_rel' := fun {p q} hpq => hle hpq } with hf
  exact ⟨w.map f⟩


theorem ctc2_isTrifurcation_of_canonical {ω : ConfigSpace (Sym2 (Site d))} {x : Site d}
    (h : IsCanonicalTrifurcation d ω x) : IsTrifurcation d ω x := by
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩ := h
  refine ⟨a₁, a₂, a₃, hne, ⟨hadj.1.reachable, hadj.2.1.reachable, hadj.2.2.reachable⟩, ?_, hsep⟩
  refine ⟨?_, ?_, ?_⟩
  · exact hinf.1.mono (ctc2_cluster_removeSite_subset x a₁ ω)
  · exact hinf.2.1.mono (ctc2_cluster_removeSite_subset x a₂ ω)
  · exact hinf.2.2.mono (ctc2_cluster_removeSite_subset x a₃ ω)


theorem ctc2_arm_in_box_succ {ω : ConfigSpace (Sym2 (Site d))} {x a : Site d} {n : ℕ}
    (hx : x ∈ box d n) (hadj : (openSubgraph d ω).Adj x a) : a ∈ box d (n + 1) :=
  arc_neighbour_in_box_succ hx hadj.1


theorem ctc2_canonical_three_disjoint_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (hxbox : x ∈ box d n) (htri : IsCanonicalTrifurcation d ω x) :
    ∃ a₁ a₂ a₃ z₁ z₂ z₃ : Site d,
      ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧
      (z₁ ∈ vertexBoundary d (n + 1) ∧ z₂ ∈ vertexBoundary d (n + 1) ∧
        z₃ ∈ vertexBoundary d (n + 1)) ∧
      (Connected d (removeSite x ω) a₁ z₁ ∧ Connected d (removeSite x ω) a₂ z₂ ∧
        Connected d (removeSite x ω) a₃ z₃) ∧
      (¬ Connected d (removeSite x ω) z₁ z₂ ∧ ¬ Connected d (removeSite x ω) z₁ z₃ ∧
        ¬ Connected d (removeSite x ω) z₂ z₃) ∧
      (z₁ ≠ z₂ ∧ z₁ ≠ z₃ ∧ z₂ ≠ z₃) := by
  obtain ⟨a₁, a₂, a₃, _, hadj, hinf, hsep⟩ := htri
  obtain ⟨z₁, z₂, z₃, hzb, hzc, hzd, hzne⟩ :=
    bk2_trif_three_disjoint_boundary ω (n + 1) (by omega)
      (ctc2_arm_in_box_succ hxbox hadj.1) (ctc2_arm_in_box_succ hxbox hadj.2.1)
      (ctc2_arm_in_box_succ hxbox hadj.2.2)
      hinf.1 hinf.2.1 hinf.2.2 hsep.1 hsep.2.1 hsep.2.2
  exact ⟨a₁, a₂, a₃, z₁, z₂, z₃, hadj, hzb, hzc, hzd, hzne⟩


theorem ctc2_armsRemoveSiteInfinite_of_canonical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x) :
    arc_TrifArmsRemoveSiteInfinite ω n := by
  intro x hxbox htri
  obtain ⟨a₁, a₂, a₃, hne, hadj, hinf, hsep⟩ := hcanon x hxbox htri
  
  refine ⟨![a₁, a₂, a₃], ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hadj.1
    · exact hadj.2.1
    · exact hadj.2.2
  · intro i
    fin_cases i
    · exact ((openSubgraph d ω).ne_of_adj hadj.1).symm
    · exact ((openSubgraph d ω).ne_of_adj hadj.2.1).symm
    · exact ((openSubgraph d ω).ne_of_adj hadj.2.2).symm
  · exact ⟨hsep.1, hsep.2.1, hsep.2.2⟩
  · intro i
    fin_cases i
    · exact hinf.1
    · exact hinf.2.1
    · exact hinf.2.2


theorem ctc2_count_of_armForestReaching (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : sfa_ArmForestReaching ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  sfa_Tcount_le_boundary_of_armForestReaching ω n h


theorem ctc2_count_single_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x : Site d} (hxbox : x ∈ box d n) (htri : IsTrifurcation d ω x)
    (hsingle : ∀ y, y ∈ box d n → IsTrifurcation d ω y → y = x)
    (c : Fin 3 → Site d)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (c i))
    (hne : ∀ i, c i ≠ x)
    (hcut : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
            ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
            ¬ Connected d (removeSite x ω) (c 1) (c 2))
    (hbdry : ∀ i, c i ∈ vertexBoundary d n)
    (hinj : Function.Injective c) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  arc_Tcount_le_boundary_of_residue_single_boundary ω n hxbox htri hsingle c hadj hne hcut
    hbdry hinj


theorem ctc2_count_of_disjointArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hdisj : bk2_DisjointArmEnds ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  bk2_Tcount_le_boundary_of_disjointArmEnds ω n hn hdisj


theorem ctc2_count_of_subsingleton (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  ctc2_count_of_disjointArmEnds ω n hn (bk2_disjointArmEnds_of_subsingleton ω n hsub)


theorem ctc2_count_of_forestLeafInjection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daec_ForestLeafInjection ω n) : Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daec_Tcount_le_boundary_of_forestLeafInjection ω n h


end Percolation
end StatMech
