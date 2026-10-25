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
import Def.StatisticalMechanics.Code.Universality.GreenStubClose
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem gst_greenMatchedFrame_iff_matchedFrameDualV (ω : ConfigSpace (Sym2 (Site 2)))
    (n : ℤ) : gec2_GreenMatchedFrame ω n ↔ mpd_MatchedFrameDualV ω n := by
  rw [gec2_matchedFrameDualV_iff_closedH]
  constructor
  · rintro ⟨x, y, hxy⟩
    exact ⟨x, y, hxy.map (gst_greenToNegHom ω n)⟩
  · intro h
    exact gec2_greenMatchedFrame_of_matchedFrameDualV ω n
      ((gec2_matchedFrameDualV_iff_closedH ω n).mpr h)


theorem gst_greenJordan_false (n : ℤ) (hn : 1 ≤ n) :
    ¬ gec2_GreenJordan des_cutConfig n := by
  rw [gec2_GreenJordan, gst_greenMatchedFrame_iff_matchedFrameDualV]
  exact gec2_cut_no_matchedFrameDualV n hn


end Universality
end StatMech
