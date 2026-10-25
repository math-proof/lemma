/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactRedesign.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWOuterStraddle.Part2
import Def.StatisticalMechanics.Code.Universality.RSWContactRedesign
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_outerExitGoodContactPair_of_traceSeparation
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hsep : RlcOuterExitTraceSeparation G hn hlt omega)
    (horder : RlcOuterExitContactArcOrder G omega) :
    Nonempty (RlcOuterExitGoodContactPair G omega) := by
  let c := mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
    (rlc_outerExitAnchor G omega)
  let q := rlc_outerExitReflectedOpenLoop G hn hlt omega
  obtain ⟨⟨xr, hxrPath, hxrQ⟩, ⟨yr, hyrPath, hyrQ⟩⟩ :=
    rlc_reflectedOpenDualCycle_contacts_both_of_straddles
      q gamma gamma' hsep.1 hsep.2
  have hqSupport : q.support = List.map rlc_dualReflect c.support := by
    simp [q, c, rlc_outerExitReflectedOpenLoop,
      rlc_dualReflectOpenWalk, SimpleGraph.Walk.support_map,
      SimpleGraph.Walk.support_mapLe_eq_support, rlc_dualReflectOpenHom]
  rw [hqSupport] at hxrQ hyrQ
  obtain ⟨x, hx, hxr⟩ := List.mem_map.mp hxrQ
  obtain ⟨y, hy, hyr⟩ := List.mem_map.mp hyrQ
  have hxPath : rlc_dualReflect x ∈ rlc_pathVertices gamma.1 := by
    simpa using hxr ▸ hxrPath
  have hyPath : rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 := by
    simpa using hyr ▸ hyrPath
  exact ⟨RlcOuterExitGoodContactPair.ofContactOrder
    horder hx hy hxPath hyPath⟩


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_traceSeparation
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hsep : RlcOuterExitTraceSeparation G hn hlt omega)
    (horder : RlcOuterExitContactArcOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  obtain ⟨hcontacts⟩ :=
    rlc_outerExitGoodContactPair_of_traceSeparation
      G hn hlt omega hsep horder
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitGoodContactPair
    G hn hlt omega hcontacts


end Universality
end StatMech
