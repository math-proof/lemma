module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
public import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
public import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
public import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
public import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
public import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
public import Theorem.StatisticalMechanics.Code.Universality.DualEventSetEquality.Part4
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
public import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
public import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
public import Theorem.StatisticalMechanics.Code.Universality.MatchedPlanarDualityClose.Part5
public import Theorem.StatisticalMechanics.Code.Universality.RSWBxpAssembly.Part2
public import Def.StatisticalMechanics.Code.Universality.GreenEdgesClosureClose.Part2
open Set SimpleGraph Finset MeasureTheory
open StatMech.Lattice
open StatMech.RSW.Box


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/GreenEdgesClosureClose.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace Universality

theorem gec2_greenMatchedFrame_of_matchedFrameDualV (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : mpd_MatchedFrameDualV ω n) : gec2_GreenMatchedFrame ω n := by
  rw [gec2_matchedFrameDualV_iff_closedH] at h
  obtain ⟨x, y, hxy⟩ := h
  exact ⟨x, y, StatMech.TwoDim.connectedWithin_mono (gec2_greenConfig_ge_negConfig ω n) hxy⟩


theorem gec2_negConfig_bot (e : Sym2 (Site 2)) : des_negConfig bcc_botCfg e = true := by
  rw [des_negConfig_apply]; simp [bcc_botCfg]


end Universality
end StatMech
