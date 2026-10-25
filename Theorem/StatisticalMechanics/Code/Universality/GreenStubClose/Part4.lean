/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenStubClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose.Part5
import Theorem.StatisticalMechanics.Code.Universality.GreenEdgesClosureClose.Part6
import Def.StatisticalMechanics.Code.Universality.GreenStubClose.Part3
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem gst_greenDualV_of_matchedFrameDualV (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : mpd_MatchedFrameDualV ω n) : gst_GreenDualV ω n := by
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, StatMech.TwoDim.connectedWithin_mono (gst_greenDualConfig_ge ω n) hxy⟩


theorem gst_nonvacuous (n : ℤ) (hn : 0 ≤ n) :
    ¬ HorizontalCrossing bcc_botCfg 0 (n + 1) 0 n ∧ gst_GreenDualV bcc_botCfg n := by
  refine ⟨mpd_botCfg_noH n hn, ?_⟩
  obtain ⟨x, y, hxy⟩ := mpd_botCfg_dualV_col (-n) 0 0 (n + 1) 0 ⟨by omega, le_refl 0⟩ (by omega)
  exact ⟨x, y, StatMech.TwoDim.connectedWithin_mono (gst_greenDualConfig_ge bcc_botCfg n) hxy⟩


theorem gst_cutEdge_open_invariant (n : ℤ) {u v : Site 2}
    (h : IsOpenEdge 2 (gst_greenDualConfig des_cutConfig n) u v) :
    (u 1 ≤ 1 ∧ v 1 ≤ 1) ∨ (u 1 = n + 1 ∧ v 1 = n + 1) := by
  obtain ⟨hadj, hopen⟩ := h
  rw [gst_greenDualConfig_open_iff] at hopen
  rcases hopen with hg | hd
  · obtain ⟨x, y, hexy, _, _, hcase⟩ := hg
    rw [Sym2.eq_iff] at hexy
    rcases hexy with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> subst hx <;> subst hy <;>
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left; omega
    · right; exact ⟨h1, h2⟩
    · left; omega
    · right; exact ⟨h2, h1⟩
  · left; exact mpd_dualCut_snd_le ⟨hadj, hd⟩


theorem gst_cut_walk_le_one (n : ℤ) (hn : 1 ≤ n) {S : Set (Site 2)} {x y : S}
    (h : ConnectedWithin 2 (gst_greenDualConfig des_cutConfig n) S x y)
    (hx : (x : Site 2) 1 ≤ 1) : (y : Site 2) 1 ≤ 1 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hx
  | @cons a b c hab _ ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    apply ih
    rcases gst_cutEdge_open_invariant n hab with ⟨_, hb⟩ | ⟨ha, _⟩
    · exact hb
    · omega


theorem gst_cut_fails (n : ℤ) (hn : 1 ≤ n) : ¬ gst_GreenDualV des_cutConfig n := by
  rintro ⟨x, y, hxy⟩
  have hx1 : ((⟨(x : Site 2), bottomSide_subset x.2⟩ : rect (-n) 0 0 (n + 1)) : Site 2) 1 ≤ 1 := by
    change (x : Site 2) 1 ≤ 1; rw [x.2.2]; norm_num
  have hy1 := gst_cut_walk_le_one n hn hxy hx1
  have : (y : Site 2) 1 ≤ 1 := hy1
  rw [y.2.2] at this; omega


end Universality
end StatMech
