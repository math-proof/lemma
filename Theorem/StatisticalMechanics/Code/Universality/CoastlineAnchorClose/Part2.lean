/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CoastlineAnchorClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Universality.JordanExhaustivityClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.PlanarMengerDualityClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.MengerBarrierClose.Part2
import Theorem.StatisticalMechanics.Code.Universality.CoastlineContinuityClose.Part2
import Def.StatisticalMechanics.Code.Universality.CoastlineAnchorClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem cac_frontierReachesBottom_of_anchor (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {a₀ b₀ : ℤ} (ha0 : 0 ≤ a₀) (ha0' : a₀ ≤ n - 1) (hb0 : -1 ≤ b₀) (hb0' : b₀ ≤ n)
    (h : cac_AllFrontierReachAnchor ω n a₀ b₀) : ccc_FrontierReachesBottom ω n :=
  ⟨a₀, b₀, ha0, ha0', hb0, hb0', h⟩


theorem cac_row0_frontier_reaches_bottom (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) {c₀ : ℤ} (h0 : mbc_IsRightFrontier ω n c₀ 0) :
    (pmd_boxFaceBarrier ω n).Reachable ![c₀, 0] ![c₀, -1] := by
  have h := ccc_frontierFace_down_adj ω n (le_refl 0) hn h0
  have he : ((0 : ℤ) - 1) = (-1 : ℤ) := by ring
  rw [he] at h
  exact h.reachable


theorem cac_anchor_in_range (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    {c₀ : ℤ} (h0 : mbc_IsRightFrontier ω n c₀ 0) :
    0 ≤ c₀ ∧ c₀ ≤ n - 1 ∧ (-1 : ℤ) ≤ -1 ∧ (-1 : ℤ) ≤ n := by
  obtain ⟨hc0, hcn, _, _⟩ := h0
  exact ⟨hc0, hcn, le_refl _, by omega⟩


end Universality
end StatMech
