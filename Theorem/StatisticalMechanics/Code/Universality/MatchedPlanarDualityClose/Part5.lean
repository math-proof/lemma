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
import Def.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose.Part4
open Set SimpleGraph Finset
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem mpd_botCfg_dualV_col (a b c d x0 : ℤ) (hx : a ≤ x0 ∧ x0 ≤ b) (hcd : c ≤ d) :
    DualVerticalCrossing bcc_botCfg a b c d := by
  unfold DualVerticalCrossing VerticalCrossing
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ d - c)
  set R := rect a b c d with hR
  have hbmem : (![x0, c] : Site 2) ∈ bottomSide a b c d := by
    refine ⟨?_, by simp⟩; rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨hx.1, hx.2, by omega, hcd⟩
  have htmem : (![x0, d] : Site 2) ∈ topSide a b c d := by
    refine ⟨?_, by simp⟩; rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; exact ⟨hx.1, hx.2, hcd, le_refl _⟩
  have hupd : ∀ t : ℕ, Function.update (![x0, c] : Site 2) 1 ((![x0, c] : Site 2) 1 + (t : ℤ))
      = ![x0, c + (t : ℤ)] := by
    intro t; funext i; fin_cases i <;> simp [Function.update]
  have hseg := segment_connectedWithin (d := 2) R (1 : Fin 2) (![x0, c] : Site 2) k
    (fun t htle => by
      rw [hR, hupd t, mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨hx.1, hx.2, by omega, by omega⟩)
  obtain ⟨w⟩ := hseg
  have wmap := w.map (mpd_dualBotHom R)
  refine ⟨⟨![x0, c], hbmem⟩, ⟨![x0, d], htmem⟩, ?_⟩
  change (openSubgraphInduce 2 (dualConfig bcc_botCfg) R).Reachable
    ⟨![x0, c], bottomSide_subset hbmem⟩ ⟨![x0, d], topSide_subset htmem⟩
  refine (wmap.copy ?_ ?_).reachable
  · apply Subtype.ext
    change Function.update (![x0, c] : Site 2) 1 ((![x0, c] : Site 2) 1 + (0 : ℤ)) = ![x0, c]
    funext i; fin_cases i <;> simp [Function.update]
  · apply Subtype.ext
    change Function.update (![x0, c] : Site 2) 1 ((![x0, c] : Site 2) 1 + ((k : ℕ) : ℤ)) = ![x0, d]
    have hck : (![x0, c] : Site 2) 1 + ((k : ℕ) : ℤ) = d := by simp; omega
    rw [hck]
    funext i; fin_cases i <;> simp [Function.update]


theorem mpd_botCfg_noH (n : ℤ) (hn : 0 ≤ n) :
    ¬ HorizontalCrossing bcc_botCfg 0 (n + 1) 0 n := by
  rintro ⟨x, y, hxy⟩
  have heq := bcc_connWithin_bot_eq hxy
  have hval : (x : Site 2) = (y : Site 2) := congrArg Subtype.val heq
  have hx0 : (x : Site 2) 0 = 0 := x.2.2
  have hy0 : (y : Site 2) 0 = n + 1 := y.2.2
  rw [hval, hy0] at hx0
  omega


theorem mpd_matchedFrame_nonvacuous (n : ℤ) (hn : 0 ≤ n) :
    ¬ HorizontalCrossing bcc_botCfg 0 (n + 1) 0 n ∧ mpd_MatchedFrameDualV bcc_botCfg n :=
  ⟨mpd_botCfg_noH n hn,
    mpd_botCfg_dualV_col (-n) 0 0 (n + 1) 0 ⟨by omega, le_refl 0⟩ (by omega)⟩


theorem mpd_literal_vs_honest_boxes (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    (DualVerticalCrossing ω 0 (n + 1) 0 n
        ↔ HorizontalCrossing (des_negConfig ω) 0 n (-(n + 1)) 0) ∧
      (mpd_MatchedFrameDualV ω n
        ↔ HorizontalCrossing (des_negConfig ω) 0 (n + 1) 0 n) := by
  refine ⟨mpd_dualV_iff_negH ω 0 (n + 1) 0 n, ?_⟩
  unfold mpd_MatchedFrameDualV
  have := mpd_dualV_iff_negH ω (-n) 0 0 (n + 1)
  simpa using this


theorem mpd_both_plain_targets_false (n : ℤ) (hn : 2 ≤ n) :
    ¬ HorizontalCrossing des_cutConfig 0 (n + 1) 0 n ∧
      ¬ DualVerticalCrossing des_cutConfig 0 (n + 1) 0 n ∧
      ¬ DualVerticalCrossing des_cutConfig (-n) 0 0 (n + 1) :=
  ⟨mpd_no_H_box (n + 1) n (by omega),
   mpd_no_dualV_box 0 (n + 1) n hn,
   mpd_corrected_box_false n (by omega)⟩

end Universality
end StatMech
