/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
import Def.StatisticalMechanics.Code.Universality.GreenEdgesClosureClose.Part3
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem gec2_negBot_horizontalCrossing (n : ℤ) (hn : 0 ≤ n) :
    HorizontalCrossing (des_negConfig bcc_botCfg) 0 (n + 1) 0 n := by
  unfold HorizontalCrossing
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ (n + 1) - 0)
  set R := rect 0 (n + 1) 0 0 with hR
  have hlmem : (![0, 0] : Site 2) ∈ leftSide 0 (n + 1) 0 n := by
    refine ⟨?_, by simp⟩; rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨le_refl 0, by omega, le_refl 0, hn⟩
  have hrmem : (![n + 1, 0] : Site 2) ∈ rightSide 0 (n + 1) 0 n := by
    refine ⟨?_, by simp⟩; rw [mem_rect]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨by omega, le_refl _, le_refl 0, hn⟩
  have hupd : ∀ t : ℕ, Function.update (![0, 0] : Site 2) 0 ((![0, 0] : Site 2) 0 + (t : ℤ))
      = ![(t : ℤ), 0] := by
    intro t; funext i; fin_cases i <;> simp [Function.update]
  have hseg := segment_connectedWithin (d := 2) (rect 0 (n + 1) 0 n) (0 : Fin 2)
    (![0, 0] : Site 2) k
    (fun t htle => by
      rw [hupd t, mem_rect]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      exact ⟨by positivity, by omega, le_refl 0, hn⟩)
  obtain ⟨w⟩ := hseg
  have wmap := w.map (gec2_negBotHom (rect 0 (n + 1) 0 n))
  refine ⟨⟨![0, 0], hlmem⟩, ⟨![n + 1, 0], hrmem⟩, ?_⟩
  change (openSubgraphInduce 2 (des_negConfig bcc_botCfg) (rect 0 (n + 1) 0 n)).Reachable
    ⟨![0, 0], leftSide_subset hlmem⟩ ⟨![n + 1, 0], rightSide_subset hrmem⟩
  refine (wmap.copy ?_ ?_).reachable
  · apply Subtype.ext
    change Function.update (![0, 0] : Site 2) 0 ((![0, 0] : Site 2) 0 + (0 : ℤ)) = ![0, 0]
    funext i; fin_cases i <;> simp [Function.update]
  · apply Subtype.ext
    change Function.update (![0, 0] : Site 2) 0 ((![0, 0] : Site 2) 0 + ((k : ℕ) : ℤ)) = ![n + 1, 0]
    have hck : (![0, 0] : Site 2) 0 + ((k : ℕ) : ℤ) = n + 1 := by
      simp only [Matrix.cons_val_zero]; omega
    rw [hck]; funext i; fin_cases i <;> simp [Function.update]


theorem gec2_greenMatchedFrame_nonvacuous (n : ℤ) (hn : 0 ≤ n) :
    ¬ HorizontalCrossing bcc_botCfg 0 (n + 1) 0 n ∧ gec2_GreenMatchedFrame bcc_botCfg n := by
  refine ⟨mpd_botCfg_noH n hn, ?_⟩
  obtain ⟨x, y, hxy⟩ := gec2_negBot_horizontalCrossing n hn
  exact ⟨x, y, StatMech.TwoDim.connectedWithin_mono
    (gec2_greenConfig_ge_negConfig bcc_botCfg n) hxy⟩


theorem gec2_cut_stub_bottom (n b : ℤ) (h0 : 0 ≤ b) (hbn : b ≤ n) :
    dualConfig des_cutConfig s(![-b, 0], ![-b, 1]) = true ∧
      (![-b, 0] : Site 2) ∈ bottomSide (-n) 0 0 (n + 1) := by
  refine ⟨?_, ?_⟩
  · rw [dual_isOpen_iff_isClosed]
    have hce : (crossEdge.symm s((![-b, 0] : Site 2), ![-b, 1]))
        = s(rot90Inv ![-b, 0], rot90Inv ![-b, 1]) := by
      change (sym2Congr rot90Equiv).symm s(_, _) = _
      rw [sym2Congr]; simp [Sym2.map_mk]
    rw [hce]
    have e1 : rot90Inv (![-b, 0] : Site 2) = ![0, b] := by funext i; fin_cases i <;> simp [rot90Inv]
    have e2 : rot90Inv (![-b, 1] : Site 2) = ![1, b] := by funext i; fin_cases i <;> simp [rot90Inv]
    rw [e1, e2]
    exact des_cutConfig_cut_closed b
  · refine ⟨?_, by simp⟩
    rw [mem_rect]; simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    exact ⟨by omega, by omega, le_refl 0, by omega⟩


theorem gec2_face_dualCircuit (ω : ConfigSpace (Sym2 (Site 2)))
    {n : ℤ} (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 (n + 1) 0 n) :
    ∃ (u : Site 2) (c : (faceBoundaryGraph (mpd_leftReach ω n)).Walk u u), c.IsCycle :=
  mpd_exists_dualCircuit ω hn hnoH


end Universality
end StatMech
