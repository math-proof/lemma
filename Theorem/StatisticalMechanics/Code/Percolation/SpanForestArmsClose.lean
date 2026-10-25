/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanForestArmsClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SingleLeafHallClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BoundaryPruningClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKSpanningTreeClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.OpenSpanningForestClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SecondPeelingClose.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem sfa_avoid_no_edge {V : Type*} {T : SimpleGraph V} {x a b : V} (w : T.Walk a b)
    (hx : x ∉ w.support) {e : Sym2 V} (he : e ∈ w.edges) : x ∉ e :=
  fun hxe => hx (w.mem_support_of_mem_edges he hxe)


theorem sfa_avoid_walk {V : Type*} {T : SimpleGraph V} {x a b : V} (ha : a ≠ x) (hb : b ≠ x)
    (h : (T.induce ({x}ᶜ : Set V)).Reachable ⟨a, by simpa using ha⟩ ⟨b, by simpa using hb⟩) :
    ∃ w : T.Walk a b, x ∉ w.support := by
  obtain ⟨w⟩ := h
  set f : (T.induce ({x}ᶜ : Set V)) →g T :=
    { toFun := fun u => (u : V), map_rel' := fun {p q} hpq => hpq } with hf
  set w' := w.map f with hw'
  refine ⟨w', ?_⟩
  intro hx
  rw [hw', Walk.support_map, List.mem_map] at hx
  obtain ⟨⟨y, hy⟩, _, hyx⟩ := hx
  rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
  exact hy (by simpa [hf] using hyx)


theorem sfa_glue_path {V : Type*} {T : SimpleGraph V} {x c0 c1 z0 z1 : V}
    (hxc0 : T.Adj x c0) (hxc1 : T.Adj x c1)
    (w0 : T.Walk c0 z0) (hw0p : w0.IsPath) (hw0x : x ∉ w0.support)
    (w1 : T.Walk c1 z1) (hw1p : w1.IsPath) (hw1x : x ∉ w1.support)
    (hdisj : ∀ v, v ∈ w0.support → v ∈ w1.support → False) :
    ∃ p : T.Walk z0 z1, p.IsPath ∧ x ∈ p.support ∧ c0 ∈ p.support ∧ c1 ∈ p.support := by
  set tw : T.Walk c0 z1 := Walk.cons hxc0.symm (Walk.cons hxc1 w1) with htw
  set p : T.Walk z0 z1 := w0.reverse.append tw with hp
  have htwsupp : tw.support = c0 :: x :: w1.support := by
    rw [htw, Walk.support_cons, Walk.support_cons]
  have hpsupp : p.support = w0.reverse.support ++ (x :: w1.support) := by
    rw [hp, Walk.support_append, htwsupp]; rfl
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · rw [Walk.isPath_def, hpsupp, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [Walk.support_reverse, List.nodup_reverse]; exact hw0p.support_nodup
    · rw [List.nodup_cons]; exact ⟨hw1x, hw1p.support_nodup⟩
    · intro a ha b hb
      rw [Walk.support_reverse, List.mem_reverse] at ha
      rw [List.mem_cons] at hb
      rcases hb with rfl | hb
      · exact fun h => hw0x (h ▸ ha)
      · exact fun h => hdisj a ha (h ▸ hb)
  · rw [hpsupp, List.mem_append, List.mem_cons]; right; left; rfl
  · rw [hpsupp, List.mem_append]; left; rw [Walk.support_reverse, List.mem_reverse]
    exact w0.start_mem_support
  · rw [hpsupp, List.mem_append, List.mem_cons]; right; right; exact w1.start_mem_support


theorem sfa_walk_avoid_connected (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    {x a b : Site d} (w : T.Walk a b) (hwx : x ∉ w.support) :
    Connected d (removeSite x ω) a b := by
  classical
  set f : T →g (openSubgraph d ω) :=
    { toFun := id, map_rel' := fun {p q} hpq => hπ p q hpq } with hf
  set ww := w.map f with hww
  have hsupp : x ∉ ww.support := by
    intro hx
    rw [hww, SimpleGraph.Walk.support_map, List.mem_map] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [hf] at hyx; subst hyx
    exact hwx hy
  exact slh_walk_avoid_transfer ww hsupp


theorem sfa_armWalks_disjoint (ω : ConfigSpace (Sym2 (Site d))) (T : SimpleGraph (Site d))
    (hπ : ∀ u v, T.Adj u v → (openSubgraph d ω).Adj u v)
    {x c0 c1 z0 z1 : Site d}
    (w0 : T.Walk c0 z0) (hw0x : x ∉ w0.support)
    (w1 : T.Walk c1 z1) (hw1x : x ∉ w1.support)
    (hcut : ¬ Connected d (removeSite x ω) c0 c1) :
    ∀ v, v ∈ w0.support → v ∈ w1.support → False := by
  classical
  intro v hv0 hv1
  apply hcut
  have h0 : Connected d (removeSite x ω) c0 v :=
    sfa_walk_avoid_connected ω T hπ (w0.takeUntil v hv0)
      (fun hx => hw0x (w0.support_takeUntil_subset_support hv0 hx))
  have h1 : Connected d (removeSite x ω) c1 v :=
    sfa_walk_avoid_connected ω T hπ (w1.takeUntil v hv1)
      (fun hx => hw1x (w1.support_takeUntil_subset_support hv1 hx))
  exact h0.trans h1.symm


end Percolation
end StatMech
