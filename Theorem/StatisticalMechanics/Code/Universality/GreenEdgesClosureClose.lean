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
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem gec2_cut_noH (n : ℤ) (hn : 1 ≤ n) :
    ¬ HorizontalCrossing des_cutConfig 0 (n + 1) 0 n := by
  rintro ⟨x, y, hxy⟩
  have hside := des_cutConfig_connectedWithin_sameSide0 hxy
  have hx0 : (x : Site 2) 0 = 0 := x.2.2
  have hy0 : (y : Site 2) 0 = n + 1 := y.2.2
  rw [hx0, hy0] at hside
  have h0 : (0 : ℤ) ≤ 0 := le_refl 0
  have : (n + 1 : ℤ) ≤ 0 := hside.mp h0
  omega


theorem gec2_cut_no_matchedFrameDualV (n : ℤ) (hn : 1 ≤ n) :
    ¬ mpd_MatchedFrameDualV des_cutConfig n :=
  mpd_corrected_box_false n hn


theorem gec2_matchedFrameDualV_false (n : ℤ) (hn : 1 ≤ n) :
    ¬ (∀ ω : ConfigSpace (Sym2 (Site 2)),
        ¬ HorizontalCrossing ω 0 (n + 1) 0 n → mpd_MatchedFrameDualV ω n) := by
  intro h
  exact gec2_cut_no_matchedFrameDualV n hn (h des_cutConfig (gec2_cut_noH n hn))


theorem gec2_rot90_rect (n : ℤ) (x : Site 2) :
    x ∈ rect 0 (n + 1) 0 n ↔ rot90Fun x ∈ rect (-n) 0 0 (n + 1) := by
  simp only [mem_rect, rot90Fun, Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> intro h <;> exact ⟨by omega, by omega, by omega, by omega⟩


theorem gec2_rot90_leftSide (n : ℤ) (x : Site 2) :
    x ∈ leftSide 0 (n + 1) 0 n ↔ rot90Fun x ∈ bottomSide (-n) 0 0 (n + 1) := by
  simp only [mem_leftSide, mem_bottomSide, mem_rect, rot90Fun,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


theorem gec2_rot90_rightSide (n : ℤ) (x : Site 2) :
    x ∈ rightSide 0 (n + 1) 0 n ↔ rot90Fun x ∈ topSide (-n) 0 0 (n + 1) := by
  simp only [mem_rightSide, mem_topSide, mem_rect, rot90Fun,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  constructor <;> rintro ⟨⟨h1, h2, h3, h4⟩, h5⟩ <;>
    exact ⟨⟨by omega, by omega, by omega, by omega⟩, by omega⟩


theorem gec2_matchedFrameDualV_iff_closedH (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    mpd_MatchedFrameDualV ω n ↔ HorizontalCrossing (des_negConfig ω) 0 (n + 1) 0 n :=
  (mpd_literal_vs_honest_boxes ω n).2


end Universality
end StatMech
