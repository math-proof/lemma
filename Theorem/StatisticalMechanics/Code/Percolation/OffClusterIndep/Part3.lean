/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.LastExit.Part2
import Def.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part2
open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


variable {d : ℕ}


theorem extract_box (ω : ConfigSpace (Sym2 (Site d))) (C : Set (Site d)) (y v : Site d) (n : ℕ)
    (hn : 1 ≤ n) (hyC : y ∉ C) (hvC : v ∉ C)
    (hybox : y ∈ box d n) (hvbox : v ∉ box d (n - 1))
    (hconn : ConnectedWithin d ω {z | z ∉ C} ⟨y, hyC⟩ ⟨v, hvC⟩) :
    ∃ (z : Site d) (hz : z ∈ box d n \ C), z ∉ box d (n - 1) ∧
      ConnectedWithin d ω (box d n \ C) ⟨y, hybox, hyC⟩ ⟨z, hz⟩ := by
  classical
  obtain ⟨w⟩ := hconn
  set G := openSubgraph d ω with hG
  have hw' : (G.induce {z : Site d | z ∉ C}).Walk ⟨y, hyC⟩ ⟨v, hvC⟩ := w
  set e := (SimpleGraph.Embedding.induce (G := G) {z : Site d | z ∉ C}) with he
  set p : G.Walk y v := (hw'.map e.toHom).copy rfl rfl with hp
  have hpC : ∀ i, p.getVert i ∉ C := by
    intro i
    have hgv : (p.getVert i) = ((hw'.getVert i : {z : Site d | z ∉ C}) : Site d) := by
      rw [hp, SimpleGraph.Walk.getVert_copy, SimpleGraph.Walk.getVert_map]; rfl
    rw [hgv]; exact (hw'.getVert i).2
  have hyT : y ∈ box d n \ C := ⟨hybox, hyC⟩
  have hDinT : ∀ i, p.getVert i ∈ box d (n - 1) → p.getVert i ∈ box d n \ C :=
    fun i hi => ⟨box_mono d (by omega) hi, hpC i⟩
  have hstep : ∀ i, i < p.length → p.getVert i ∈ box d (n - 1) →
      p.getVert (i + 1) ∈ box d n \ C := by
    intro i hi hiD
    have hadj' : (hypercubicLattice d).Adj (p.getVert i) (p.getVert (i + 1)) :=
      (p.adj_getVert_succ hi).1
    refine ⟨?_, hpC (i + 1)⟩
    have := adj_box_step hiD hadj'; rwa [show n - 1 + 1 = n from by omega] at this
  obtain ⟨z, hzT, hzD, ⟨ww⟩⟩ :=
    exists_firstExit_induce p (box d (n - 1)) (box d n \ C) hyT hvbox hDinT hstep
  exact ⟨z, hzT, hzD, ⟨ww⟩⟩


theorem connWithinR_congr (R : Set (Site d)) {a b : Site d} (ha : a ∈ R) (hb : b ∈ R)
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (h : ∀ x ∈ R, ∀ z ∈ R, ω s(x, z) = ω' s(x, z)) :
    ConnectedWithin d ω R ⟨a, ha⟩ ⟨b, hb⟩ ↔ ConnectedWithin d ω' R ⟨a, ha⟩ ⟨b, hb⟩ := by
  have hG : openSubgraphInduce d ω R = openSubgraphInduce d ω' R := by
    apply SimpleGraph.ext
    ext aa bb
    simp only [openSubgraphInduce_adj, openSubgraph_adj]
    rw [h aa aa.2 bb bb.2]
  unfold ConnectedWithin
  rw [hG]


end Percolation
end StatMech
