/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MatchedPlanarDualityClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWFrameReconcileClose.Part3
import Def.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose
open Set SimpleGraph Finset
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem mpd_dualV_iff_negH (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) :
    DualVerticalCrossing ω a b c d ↔ HorizontalCrossing (des_negConfig ω) c d (-b) (-a) := by
  constructor
  · rintro ⟨x, y, hxy⟩
    refine ⟨⟨rot90Inv (x : Site 2), (mpd_rot90Inv_bottomSide a b c d x).1 x.2⟩,
            ⟨rot90Inv (y : Site 2), (mpd_rot90Inv_topSide a b c d y).1 y.2⟩, ?_⟩
    exact (hxy : (openSubgraphInduce 2 (dualConfig ω) (rect a b c d)).Reachable _ _).map
      (mpd_inducedHom a b c d ω)
  · rintro ⟨x, y, hxy⟩
    refine ⟨⟨rot90Fun (x : Site 2), ?_⟩, ⟨rot90Fun (y : Site 2), ?_⟩, ?_⟩
    · rw [mpd_rot90Inv_bottomSide a b c d, show rot90Inv (rot90Fun (x : Site 2)) = (x : Site 2) from
        rot90Equiv.left_inv (x : Site 2)]; exact x.2
    · rw [mpd_rot90Inv_topSide a b c d, show rot90Inv (rot90Fun (y : Site 2)) = (y : Site 2) from
        rot90Equiv.left_inv (y : Site 2)]; exact y.2
    · exact (hxy : (openSubgraphInduce 2 (des_negConfig ω) (rect c d (-b) (-a))).Reachable _ _).map
        (mpd_inducedHomInv a b c d ω)


theorem mpd_dualCut_snd_le {p q : Site 2}
    (h : IsOpenEdge 2 (dualConfig des_cutConfig) p q) : p 1 ≤ 1 ∧ q 1 ≤ 1 := by
  obtain ⟨_hadj, hopen⟩ := h
  rw [dual_isOpen_iff_isClosed] at hopen
  have hce : (crossEdge.symm s(p, q)) = s(rot90Inv p, rot90Inv q) := by
    change (sym2Congr rot90Equiv).symm s(p, q) = s(rot90Inv p, rot90Inv q)
    rw [sym2Congr]; simp [Sym2.map_mk]
  rw [hce] at hopen
  by_contra hcon
  apply absurd hopen
  rw [des_cutConfig_open_of_not_cut]
  · simp
  · rintro ⟨c, hc⟩
    rw [Sym2.eq_iff] at hc
    rcases hc with ⟨hp, hq⟩ | ⟨hp, hq⟩
    · have hp1 : p 1 = 0 := by have := congrFun hp 0; simpa [rot90Inv] using this
      have hq1 : q 1 = 1 := by have := congrFun hq 0; simpa [rot90Inv] using this
      omega
    · have hp1 : p 1 = 1 := by have := congrFun hp 0; simpa [rot90Inv] using this
      have hq1 : q 1 = 0 := by have := congrFun hq 0; simpa [rot90Inv] using this
      omega


theorem mpd_dualCut_walk_snd_le {S : Set (Site 2)} {x y : S}
    (h : ConnectedWithin 2 (dualConfig des_cutConfig) S x y)
    (hx : (x : Site 2) 1 ≤ 1) : (y : Site 2) 1 ≤ 1 := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact hx
  | @cons a b c hab _ ih =>
    rw [openSubgraphInduce_adj, openSubgraph_adj] at hab
    exact ih (mpd_dualCut_snd_le hab).2


theorem mpd_no_dualV_box (a b h : ℤ) (hh : 2 ≤ h) :
    ¬ DualVerticalCrossing des_cutConfig a b 0 h := by
  rw [dualVerticalCrossing_iff]
  rintro ⟨x, y, hxy⟩
  have hx1 : ((⟨(x : Site 2), bottomSide_subset x.2⟩ : rect a b 0 h) : Site 2) 1 ≤ 1 := by
    change (x : Site 2) 1 ≤ 1; rw [x.2.2]; norm_num
  have hy1 := mpd_dualCut_walk_snd_le hxy hx1
  have : (y : Site 2) 1 ≤ 1 := hy1
  rw [y.2.2] at this
  omega


theorem mpd_no_H_box (w h : ℤ) (hw : 1 ≤ w) :
    ¬ HorizontalCrossing des_cutConfig 0 w 0 h := by
  rintro ⟨x, y, hxy⟩
  have hside := des_cutConfig_connectedWithin_sameSide0 hxy
  have hx0 : (x : Site 2) 0 = 0 := x.2.2
  have hy0 : (y : Site 2) 0 = w := y.2.2
  rw [hx0, hy0] at hside
  have h0 : (0 : ℤ) ≤ 0 := le_refl 0
  have : (w : ℤ) ≤ 0 := hside.mp h0
  omega


theorem mpd_matched_planarDuality_false (n : ℤ) (hn : 2 ≤ n) :
    ¬ rfr_MatchedPlanarDuality n := by
  intro h
  apply mpd_no_dualV_box 0 (n + 1) n hn
  have hmem : des_cutConfig ∈ dualVerticalCrossingEvent 0 (n + 1) 0 n := by
    apply h
    simp only [Set.mem_compl_iff, mem_horizontalCrossingEvent]
    exact mpd_no_H_box (n + 1) n (by omega)
  rwa [mem_dualVerticalCrossingEvent] at hmem


theorem mpd_corrected_box_false (n : ℤ) (hn : 1 ≤ n) :
    ¬ DualVerticalCrossing des_cutConfig (-n) 0 0 (n + 1) :=
  mpd_no_dualV_box (-n) 0 (n + 1) (by omega)


end Universality
end StatMech
