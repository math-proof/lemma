/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWOuterStraddle.Part2
import Def.StatisticalMechanics.Code.Universality.RSWRayTransport.Part4
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_endpointSides_of_reflectedRegion_xor
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    {a : Site 2} (C : (hypercubicLattice 2).Walk a a)
    (K : Set (Site 2))
    (hregion : rlc_reflectedPrimalRegion K = jec_leftRegion C)
    (hxor : RlcReflectedEndpointXor gamma gamma' K) :
    rlc_OppositeLoopSides C
        (gamma.1.1 : Site 2) (gamma.1.2.1 : Site 2) ∧
      rlc_OppositeLoopSides C
        (gamma'.1.1 : Site 2) (gamma'.1.2.1 : Site 2) := by
  constructor
  · rw [rlc_oppositeLoopSides_iff_leftRegion_xor, ← hregion]
    rcases hxor with ⟨hxor, _⟩
    by_cases hstart : (gamma.1.1 : Site 2) ∈ rlc_reflectedPrimalRegion K
    · by_cases hend : (gamma.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K
      · exact False.elim (hxor (propext ⟨fun _ => hend, fun _ => hstart⟩))
      · exact Or.inl ⟨hstart, hend⟩
    · by_cases hend : (gamma.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K
      · exact Or.inr ⟨hstart, hend⟩
      · exact False.elim (hxor (propext ⟨fun h => False.elim (hstart h),
          fun h => False.elim (hend h)⟩))
  · rw [rlc_oppositeLoopSides_iff_leftRegion_xor, ← hregion]
    rcases hxor with ⟨_, hxor⟩
    by_cases hstart : (gamma'.1.1 : Site 2) ∈ rlc_reflectedPrimalRegion K
    · by_cases hend : (gamma'.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K
      · exact False.elim (hxor (propext ⟨fun _ => hend, fun _ => hstart⟩))
      · exact Or.inl ⟨hstart, hend⟩
    · by_cases hend : (gamma'.1.2.1 : Site 2) ∈ rlc_reflectedPrimalRegion K
      · exact Or.inr ⟨hstart, hend⟩
      · exact False.elim (hxor (propext ⟨fun h => False.elim (hstart h),
          fun h => False.elim (hend h)⟩))


theorem rlc_outerExitEndpointSides_of_reflectedRegion_xor
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hregion : rlc_reflectedPrimalRegion
        (rlc_mixedWiredReachSet G omega) =
      jec_leftRegion
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _)))
    (hxor : RlcReflectedEndpointXor gamma gamma'
      (rlc_mixedWiredReachSet G omega)) :
    RlcOuterExitEndpointSides G hn hlt omega := by
  exact rlc_endpointSides_of_reflectedRegion_xor _ _ hregion hxor


theorem rlc_outerExitGoodContactPair_of_endpointSides
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hsides : RlcOuterExitEndpointSides G hn hlt omega)
    (horder : RlcOuterExitContactArcOrder G omega) :
    Nonempty (RlcOuterExitGoodContactPair G omega) := by
  let c := mpl_orbitFaceLoop (rlc_mixedWiredReachSet G omega)
    (rlc_outerExitAnchor G omega)
  let q := rlc_outerExitReflectedOpenLoop G hn hlt omega
  obtain ⟨hright, hleft⟩ :=
    rlc_outerExit_both_straddles_of_endpointSides G hn hlt omega hsides
  obtain ⟨⟨xr, hxrPath, hxrQ⟩, ⟨yr, hyrPath, hyrQ⟩⟩ :=
    rlc_reflectedOpenDualCycle_contacts_both_of_straddles
      q gamma gamma' hright hleft
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


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_reflectedRegion_xor
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hregion : rlc_reflectedPrimalRegion
        (rlc_mixedWiredReachSet G omega) =
      jec_leftRegion
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _)))
    (hxor : RlcReflectedEndpointXor gamma gamma'
      (rlc_mixedWiredReachSet G omega))
    (horder : RlcOuterExitContactArcOrder G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  have hsides : RlcOuterExitEndpointSides G hn hlt omega :=
    rlc_outerExitEndpointSides_of_reflectedRegion_xor
      G hn hlt omega hregion hxor
  have hcontacts : Nonempty (RlcOuterExitGoodContactPair G omega) :=
    rlc_outerExitGoodContactPair_of_endpointSides
      G hn hlt omega hsides horder
  obtain ⟨hcontacts⟩ := hcontacts
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_outerExitGoodContactPair
    G hn hlt omega hcontacts


theorem rlc_not_outerExitEndpointSides_of_failure_of_directRegionEq
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hno : omega ∉ rlc_mixedWiredConnectorEvent G)
    (hregion : rlc_mixedWiredReachSet G omega =
      jec_leftRegion
        ((rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
          (rlc_openSubgraph_le_lattice _))) :
    ¬ RlcOuterExitEndpointSides G hn hlt omega := by
  let C := (rlc_outerExitReflectedOpenLoop G hn hlt omega).mapLe
    (rlc_openSubgraph_le_lattice _)
  obtain ⟨hr0, hr1, hl0, hl1⟩ :=
    rlc_mixedWiredReachSet_separates_traceEndpoints_of_failure G omega hno
  intro hsides
  have hr0' : (gamma.1.1 : Site 2) ∈ jec_leftRegion C := by
    rw [← hregion]
    exact hr0
  have hr1' : (gamma.1.2.1 : Site 2) ∈ jec_leftRegion C := by
    rw [← hregion]
    exact hr1
  exact (rlc_not_oppositeLoopSides_of_both_mem_leftRegion C hr0' hr1')
    hsides.1

end Universality
end StatMech
