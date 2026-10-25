/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PrivateArmProve.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem pap_meets_at_most_one_branch (ω : ConfigSpace (Sym2 (Site d))) {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₂ v) ∧
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₃ v) ∧
    ¬ (Connected d (removeSite x ω) a₂ v ∧ Connected d (removeSite x ω) a₃ v) :=
  daepf_arm_class_unique ω hd12 hd13 hd23 v


theorem pap_two_branches_avoid_vertex (ω : ConfigSpace (Sym2 (Site d)))
    {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v) ∨
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₃ v) ∨
    (¬ Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₃ v) :=
  daep2_two_branches_avoid ω hd12 hd13 hd23 v


theorem pap_exists_private_branch (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x a₁ a₂ a₃ : Site d}
    (ha1box : a₁ ∈ box d n) (ha2box : a₂ ∈ box d n) (_ha3box : a₃ ∈ box d n)
    (hc1 : Connected d ω x a₁) (hc2 : Connected d ω x a₂) (_hc3 : Connected d ω x a₃)
    (hi1 : (cluster d (removeSite x ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite x ω) a₂).Infinite)
    (_hi3 : (cluster d (removeSite x ω) a₃).Infinite)
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    ∃ a, a ∈ box d n ∧ Connected d ω x a ∧ (cluster d (removeSite x ω) a).Infinite ∧
      ¬ Connected d (removeSite x ω) a v := by
  rcases pap_two_branches_avoid_vertex ω hd12 hd13 hd23 v with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h2, _⟩
  · exact ⟨a₁, ha1box, hc1, hi1, h1⟩
  · exact ⟨a₁, ha1box, hc1, hi1, h1⟩
  · exact ⟨a₂, ha2box, hc2, hi2, h2⟩


theorem pap_adj_removeSite_of_avoid (ω : ConfigSpace (Sym2 (Site d))) {x u w : Site d}
    (hu : u ≠ x) (hw : w ≠ x) (hadj : (openSubgraph d ω).Adj u w) :
    (openSubgraph d (removeSite x ω)).Adj u w := by
  rw [openSubgraph_adj] at hadj ⊢
  refine ⟨hadj.1, ?_⟩
  have hxnot : x ∉ s(u, w) := by
    rw [Sym2.mem_iff, not_or]; exact ⟨fun h => hu h.symm, fun h => hw h.symm⟩
  rw [removeSite_apply_of_notMem hxnot]; exact hadj.2


theorem pap_connected_removeSite_of_walk_avoid (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    {u w : Site d} (p : (openSubgraph d ω).Walk u w) (hx : x ∉ p.support) :
    Connected d (removeSite x ω) u w := by
  induction p with
  | nil => exact connected_rfl
  | @cons a b c hadj p' ih =>
    
    rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hx
    obtain ⟨hxa, hxrest⟩ := hx
    
    have hxb : x ≠ b := fun h => hxrest (h ▸ p'.start_mem_support)
    have hstep : (openSubgraph d (removeSite x ω)).Adj a b :=
      pap_adj_removeSite_of_avoid ω (Ne.symm hxa) (Ne.symm hxb) hadj
    exact (SimpleGraph.Adj.reachable hstep).trans (ih hxrest)


theorem pap_far_of_avoiding_path (ω : ConfigSpace (Sym2 (Site d))) {x y by_ : Site d}
    (p : (openSubgraph d ω).Walk by_ y) (hx : x ∉ p.support) :
    Connected d (removeSite x ω) by_ y :=
  pap_connected_removeSite_of_walk_avoid ω x p hx


end Percolation
end StatMech
