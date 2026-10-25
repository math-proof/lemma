/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWDualVCrossingClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.DualCutToPath.Part4
import Theorem.StatisticalMechanics.Code.Universality.DualCircuitToWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.PlanarDualCutConnected.Part5
import Theorem.StatisticalMechanics.Code.Universality.FaceDualDichotomy
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Def.StatisticalMechanics.Code.Universality.RSWDualVCrossingClose
open Set SimpleGraph
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem rdv_no_frameReconcile : ¬ ∃ Φ : Site 2 → Site 2, rdv_FrameReconcile Φ :=
  fci_no_open_dual_relabel


theorem rdv_no_frameChangeIso : ¬ ∃ Φ : Site 2 → Site 2, fci_FrameCompat Φ :=
  fci_no_frameChangeIso


theorem rdv_residue_strength (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    {v w : Site 2} (hv : v ∈ bcd_leftReach ω n) (hwbox : w ∈ rect 0 n 0 n)
    (hadj : (hypercubicLattice 2).Adj v w) (hw : w ∉ bcd_leftReach ω n) :
    (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w) :=
  fdd_leftReach_barrierEdge_dualAdj ω n hv hwbox hadj hw


theorem rdv_face_frame_dichotomy (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ) (hn : 0 ≤ n)
    (hnoH : ¬ HorizontalCrossing ω 0 n 0 n) :
    (bcd_leftReach ω n).Finite ∧
      (∀ {v w : Site 2}, v ∈ bcd_leftReach ω n → w ∈ rect 0 n 0 n →
        (hypercubicLattice 2).Adj v w → w ∉ bcd_leftReach ω n →
        (openSubgraph 2 (dualConfig ω)).Adj (rot90Fun v) (rot90Fun w)) ∧
      (∃ f g : Site 2, (faceBoundaryGraph (bcd_leftReach ω n)).Adj f g) ∧
      (∃ (u : Site 2) (c : (faceBoundaryGraph (bcd_leftReach ω n)).Walk u u),
        c.IsCycle ∧ (fci_faceWalk_to_dualWalk (bcd_leftReach ω n) c).IsCycle) :=
  fci_square_dichotomy ω n hn hnoH


theorem rdv_both_targets_false_on_witness :
    ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 ∧
      ¬ jex_DualBarrierVCrossing bcc_wallCfg 2 ∧
      ¬ dcp_DualCutConnectsRot bcc_wallCfg 2 :=
  ⟨bcc_noH_wall, bcc_noV_wall, rdv_rotResidue_false_on_noH⟩


theorem rdv_witness_separates {x y : Site 2}
    (hx : x ∈ leftSide 0 2 0 2) (hy : y ∈ rightSide 0 2 0 2) :
    ¬ (latticeMinusBarrier (bcd_leftReach bcc_wallCfg 2)).Reachable x y :=
  jex_leftReach_separates bcc_wallCfg 2 bcc_noH_wall hx hy

end Universality
end StatMech
