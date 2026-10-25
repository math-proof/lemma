/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BoxArcConnectsClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
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
import Theorem.StatisticalMechanics.Code.Universality.CircuitReachClose.Part2
import Def.StatisticalMechanics.Code.Universality.BoxArcConnectsClose.Part3
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem bac_reachesBottom_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : ccc_FrontierReachesBottom ω n := by
  obtain ⟨c₀, hc₀⟩ := mbc_exists_rightFrontier ω n hn hnoH (le_refl 0) hn
  obtain ⟨hc0, hcn, _, _⟩ := id hc₀
  refine cac_frontierReachesBottom_of_anchor ω n hc0 hcn (le_refl _) (by omega : (-1 : ℤ) ≤ n) ?_
  intro r hr0 hrn c hc
  
  have hreach0 : (pmd_boxFaceBarrier ω n).Reachable ![c, r] ![c₀, 0] :=
    hres c₀ hc₀ ![c, r] (bac_frontierFace_isRCoast ω n hnoH hr0 hrn hc)
  
  exact hreach0.trans (cac_row0_frontier_reaches_bottom ω n hn hc₀)


theorem bac_frontierArcReaches_of_rCoastConnected (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n)
    (hres : bac_RCoastConnected ω n) : crc2_FrontierArcReaches ω n :=
  crc2_arc_of_atom ω n hn (bac_reachesBottom_of_rCoastConnected ω n hn hnoH hres)


end Universality
end StatMech
