/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/PlanarDualCutConnected.lean -/

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
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.FaceRegion.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.DualCutToPath.Part4
import Def.StatisticalMechanics.Code.Universality.PlanarDualCutConnected.Part4
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

variable {ω : ConfigSpace (Sym2 (Site 2))} {n : ℤ}


theorem pdc_DualCutConnectsRot_of_primalConnects (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : pdc_PrimalBarrierConnects ω n) : dcp_DualCutConnectsRot ω n := by
  obtain ⟨a, ha, b, hb, hreach⟩ := h
  refine ⟨rot90Fun a, dcp_rot90_leftSide n ha, rot90Fun b, dcp_rot90_rightSide n hb, ?_⟩
  exact pdc_dualReach_of_primalReach ω n hreach


theorem pdc_rotatedDualVerticalCrossing_of_primalConnects
    (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (h : pdc_PrimalBarrierConnects ω n) :
    DualVerticalCrossing ω (-n) 0 0 n :=
  dcp_rotatedDualVerticalCrossing_of_cutConnectsRot ω n
    (pdc_DualCutConnectsRot_of_primalConnects ω n h)


theorem pdc_bottomBarrierEdge_primal (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v w : Site 2, (pdc_barrierGraphPrimal ω n).Adj v w ∧ v 1 = 0 ∧ w 1 = 0 := by
  obtain ⟨v, w, hbar, hv0, hw0⟩ := dcw_barrierEdge_exists ω n hn hnoH
  exact ⟨v, w, ⟨v, w, hbar, Or.inl ⟨rfl, rfl⟩⟩, hv0, hw0⟩


theorem pdc_topBarrierEdge_primal (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ v w : Site 2, (pdc_barrierGraphPrimal ω n).Adj v w ∧ v 1 = n ∧ w 1 = n := by
  obtain ⟨v, w, hbar, hvn, hwn⟩ := dcp_topBarrierEdge_exists ω n hn hnoH
  exact ⟨v, w, ⟨v, w, hbar, Or.inl ⟨rfl, rfl⟩⟩, hvn, hwn⟩


theorem pdc_primalBarrier_nonempty_edge (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (hn : 0 ≤ n) (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    ∃ a b : Site 2, (pdc_barrierGraphPrimal ω n).Adj a b := by
  obtain ⟨v, w, hadj, _, _⟩ := pdc_bottomBarrierEdge_primal ω n hn hnoH
  exact ⟨v, w, hadj⟩


end Universality
end StatMech
