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
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem cac_boxFaceBarrier_le_faceBoundaryGraph (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) :
    pmd_boxFaceBarrier ω n ≤ faceBoundaryGraph (bcd_leftReach ω n) := by
  rintro f g ⟨hadj, p, q, hpq, hbd, _hp, _hq⟩
  exact ⟨hadj, by rw [hpq]; exact hbd⟩


theorem cac_barrier_reach_lifts (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) {f g : Site 2}
    (h : (pmd_boxFaceBarrier ω n).Reachable f g) :
    (faceBoundaryGraph (bcd_leftReach ω n)).Reachable f g :=
  h.mono (cac_boxFaceBarrier_le_faceBoundaryGraph ω n)


theorem cac_dualCircuit_exists (ω : ConfigSpace (Sym2 (Site 2))) {n : ℤ}
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) {c : ℤ} (hc0 : 0 ≤ c) (hcn : c ≤ n) :
    ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u), cyc.IsCycle :=
  jex_exists_dualCircuit ω hn hnoH hc0 hcn


end Universality
end StatMech
