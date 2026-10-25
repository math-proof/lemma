/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/CircuitReachClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.CoastlineAnchorClose.Part3
import Def.StatisticalMechanics.Code.Universality.CircuitReachClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem crc2_boxBarrier_adj_of_interior (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f g : Site 2}
    (hfb : (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g)
    (hint : crc2_IsBoxInteriorEdge n f g) :
    (pmd_boxFaceBarrier ω n).Adj f g := by
  obtain ⟨p, q, hpq, hp, hq⟩ := hint
  refine ⟨hfb.1, p, q, hpq, ?_, hp, hq⟩
  have := faceBoundaryGraph_sharedPrimalEdge_bdEdge _ hfb
  rwa [hpq] at this


theorem crc2_walk_lift (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {u v : Site 2}
    (w : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u v)
    (hint : ∀ f g : Site 2, s(f, g) ∈ w.edges → crc2_IsBoxInteriorEdge n f g) :
    (pmd_boxFaceBarrier ω n).Reachable u v := by
  refine ⟨w.transfer (pmd_boxFaceBarrier ω n) ?_⟩
  intro e he
  refine e.ind (fun f g hfg => ?_) he
  rw [SimpleGraph.mem_edgeSet]
  exact crc2_boxBarrier_adj_of_interior ω n (w.adj_of_mem_edges hfg) (hint f g hfg)


theorem crc2_frontier_down_edge_interior (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {c r : ℤ}
    (hr0 : 0 ≤ r) (hrn : r ≤ n) (htr : mbc_IsRightFrontier ω n c r) :
    crc2_IsBoxInteriorEdge n ![c, r] ![c, r - 1] := by
  obtain ⟨hc0, hcn, _hcL, _hmax⟩ := htr
  refine ⟨![c, r], ![c + 1, r], ?_, ?_, ?_⟩
  · rw [sharedPrimalEdge_bottom]; unfold faceCorner00 faceCorner10; rfl
  · rw [mem_rect]
    exact ⟨by simpa using hc0, by simp; omega, by simpa using hr0, by simpa using hrn⟩
  · rw [mem_rect]
    exact ⟨by simp; omega, by simp; omega, by simpa using hr0, by simpa using hrn⟩


end Universality
end StatMech
