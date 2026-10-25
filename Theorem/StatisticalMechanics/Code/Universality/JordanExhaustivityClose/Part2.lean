/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/JordanExhaustivityClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomy
import Theorem.StatisticalMechanics.Code.Universality.BoxCrossingDichotomyClose.Part3
import Def.StatisticalMechanics.Code.Universality.JordanExhaustivityClose
open Set SimpleGraph Finset
open StatMech.Lattice
open StatMech.RSW.Box


namespace StatMech

namespace Universality

theorem jex_native_dualVerticalCrossing_of_barrier (ω : ConfigSpace (Sym2 (Site 2)))
    (n : ℤ) (h : jex_DualBarrierVCrossing ω n) :
    DualVerticalCrossing ω 0 n 0 n :=
  h


theorem jex_exhaustivity_of_barrier (ω : ConfigSpace (Sym2 (Site 2))) (n : ℤ)
    (_hnoH : ¬ HorizontalCrossing ω 0 n 0 n) (h : jex_DualBarrierVCrossing ω n) :
    HorizontalCrossing ω 0 n 0 n ∨ DualVerticalCrossing ω 0 n 0 n :=
  Or.inr (jex_native_dualVerticalCrossing_of_barrier ω n h)


theorem jex_barrier_vcrossing_nonvacuous :
    jex_DualBarrierVCrossing bcc_botCfg 2 :=
  bcc_dualVert_botCfg


theorem jex_wall_noH : ¬ HorizontalCrossing bcc_wallCfg 0 2 0 2 :=
  bcc_noH_wall


theorem jex_wall_separates {x y : Site 2}
    (hx : x ∈ leftSide 0 2 0 2) (hy : y ∈ rightSide 0 2 0 2) :
    ¬ (latticeMinusBarrier (bcd_leftReach bcc_wallCfg 2)).Reachable x y :=
  jex_leftReach_separates bcc_wallCfg 2 bcc_noH_wall hx hy


theorem jex_wall_dualCircuit :
    ∃ (u : Site 2) (cyc : (faceBoundaryGraph (bcd_leftReach bcc_wallCfg 2)).Walk u u),
      cyc.IsCycle :=
  jex_exists_dualCircuit bcc_wallCfg (by norm_num) bcc_noH_wall (c := 0) (by norm_num)
    (by norm_num)

end Universality
end StatMech
