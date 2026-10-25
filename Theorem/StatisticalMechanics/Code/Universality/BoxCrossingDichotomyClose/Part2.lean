/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxCrossingDichotomyClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Def.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part2
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem bcc_connWithin_bot_eq {S : Set (Site 2)} {x y : S}
    (h : ConnectedWithin 2 bcc_botCfg S x y) : x = y := by
  unfold ConnectedWithin at h
  obtain ⟨w⟩ := h
  cases w with
  | nil => rfl
  | cons hadj p =>
    exfalso
    rw [openSubgraphInduce_adj] at hadj
    simp only [openSubgraph_adj, bcc_botCfg] at hadj
    exact absurd hadj.2 (by decide)


theorem bcc_leftReach_bot_eq (n : ℤ) :
    bcd_leftReach bcc_botCfg n = leftSide 0 n 0 n := by
  ext v
  constructor
  · rintro ⟨hvbox, x, hxL, hvbox', hconn⟩
    have hxv : (⟨x, leftSide_subset hxL⟩ : (rect 0 n 0 n : Set (Site 2))) = ⟨v, hvbox'⟩ :=
      bcc_connWithin_bot_eq hconn
    have hxveq : x = v := congrArg Subtype.val hxv
    rw [← hxveq]; exact hxL
  · intro hv
    refine ⟨leftSide_subset hv, v, hv, leftSide_subset hv, ?_⟩
    exact connectedWithin_refl bcc_botCfg (rect 0 n 0 n) ⟨v, leftSide_subset hv⟩


theorem bcc_barrier_bot_char {v w : Site 2} (h : dcw_isBarrierEdge bcc_botCfg 2 v w) :
    v 0 = 0 ∧ v 1 = w 1 ∧ w 0 = 1 := by
  obtain ⟨hvL, hwbox, hwnL, hadj⟩ := h
  rw [bcc_leftReach_bot_eq] at hvL hwnL
  have hv0 : v 0 = 0 := hvL.2
  rw [mem_rect] at hwbox
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  have hwL : ¬ (w ∈ rect 0 2 0 2 ∧ w 0 = 0) := by
    simpa [leftSide, mem_rect] using hwnL
  have hw0 : w 0 ≠ 0 := fun hw00 => hwL ⟨by rw [mem_rect]; exact hwbox, hw00⟩
  rw [hv0] at hadj
  refine ⟨hv0, by omega, by omega⟩


theorem bcc_dualBarrier_bot_snd_le {p q : Site 2}
    (h : (dcw_dualBarrierGraph bcc_botCfg 2).Adj p q) : p 1 ≤ 1 ∧ q 1 ≤ 1 := by
  obtain ⟨v, w, hvw, hpq⟩ := h
  obtain ⟨hv0, _hvw1, hw0⟩ := bcc_barrier_bot_char hvw
  have hrv1 : (rot90Fun v) 1 = v 0 := by simp [rot90Fun]
  have hrw1 : (rot90Fun w) 1 = w 0 := by simp [rot90Fun]
  rcases hpq with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq, hrv1, hrw1, hv0, hw0]; omega
  · rw [hp, hq, hrw1, hrv1, hv0, hw0]; omega


theorem bcc_barrier_walk_snd_le {p q : Site 2}
    (c : (dcw_dualBarrierGraph bcc_botCfg 2).Walk p q) (hp : p 1 ≤ 1) :
    ∀ z ∈ c.support, z 1 ≤ 1 := by
  induction c with
  | nil =>
    intro z hz
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    subst hz; exact hp
  | @cons a b d hab pw ih =>
    intro z hz
    have hab' := bcc_dualBarrier_bot_snd_le hab
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hp
    · exact ih hab'.2 z hz


theorem bcc_barrierRoute_false : ¬ dcw_BarrierRoute bcc_botCfg 2 := by
  rintro ⟨p₀, hp₀, q₀, hq₀, c, _hsupp⟩
  have hp0 : p₀ 1 = 0 := hp₀.2
  have hq0 : q₀ 1 = 2 := hq₀.2
  have hsnd := bcc_barrier_walk_snd_le c (by rw [hp0]; norm_num) q₀ c.end_mem_support
  rw [hq0] at hsnd
  norm_num at hsnd


theorem bcc_dualConfig_bot (e : Sym2 (Site 2)) : dualConfig bcc_botCfg e = true := by
  simp [dualConfig, bcc_botCfg]


theorem bcc_dualVert_botCfg : DualVerticalCrossing bcc_botCfg 0 2 0 2 := by
  unfold DualVerticalCrossing VerticalCrossing
  have hb : (![0,0] : Site 2) ∈ bottomSide 0 2 0 2 := by
    refine ⟨?_, by simp⟩; rw [mem_rect]; exact ⟨by simp, by simp, by simp, by simp⟩
  have ht : (![0,2] : Site 2) ∈ topSide 0 2 0 2 := by
    refine ⟨?_, by simp⟩; rw [mem_rect]; exact ⟨by simp, by simp, by simp, by simp⟩
  refine ⟨⟨![0,0], hb⟩, ⟨![0,2], ht⟩, ?_⟩
  have a01 : (openSubgraph 2 (dualConfig bcc_botCfg)).Adj ![0,0] ![0,1] := by
    rw [openSubgraph_adj]; refine ⟨?_, bcc_dualConfig_bot _⟩
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  have a12 : (openSubgraph 2 (dualConfig bcc_botCfg)).Adj ![0,1] ![0,2] := by
    rw [openSubgraph_adj]; refine ⟨?_, bcc_dualConfig_bot _⟩
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; simp
  set W : (openSubgraph 2 (dualConfig bcc_botCfg)).Walk ![0,0] ![0,2] :=
    a01.toWalk.append a12.toWalk with hW
  have hsupp : ∀ z ∈ W.support, z ∈ rect 0 2 0 2 := by
    intro z hz
    have hl : W.support = [![(0:ℤ),0], ![(0:ℤ),1], ![(0:ℤ),2]] := by rw [hW]; simp
    rw [hl] at hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with h | h | h <;>
      (subst h; rw [mem_rect]; exact ⟨by simp, by simp, by simp, by simp⟩)
  exact walk_induce_reachable (openSubgraph 2 (dualConfig bcc_botCfg)) (rect 0 2 0 2) W hsupp
    (bottomSide_subset hb) (topSide_subset ht)


end Universality
end StatMech
