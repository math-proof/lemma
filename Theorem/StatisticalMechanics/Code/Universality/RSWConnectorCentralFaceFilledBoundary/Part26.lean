/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorCentralFaceFilledBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceJordan.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Def.StatisticalMechanics.Code.Universality.RSWConnectorCentralFaceFilledBoundary.Part22
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

open StatMech.Walls

noncomputable section

theorem rlc_goodComponentContacts_or_lowestAnchor_lower_or_upper_orderBadExit_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho ∨
      RlcCentralFaceLowestAnchorLowerOrderBadExit gamma gamma' rho ∨
      RlcCentralFaceLowestAnchorUpperOrderBadExit gamma gamma' rho := by
  rcases
      rlc_goodComponentContacts_or_lowestAnchorOrderedBadExit_of_faithful_failure
        gamma gamma' hfaith rho hno with hgood | ⟨L, hbad⟩
  · exact Or.inl hgood
  · obtain ⟨a, f, g, k, ha, haEdges, hfg, hreflected, hk | hk⟩ :=
      L.complementary_axis_crossing_extreme
    · exact Or.inr (Or.inl ⟨L, hbad,
        a, f, g, k, ha, haEdges, hfg, hreflected, hk⟩)
    · exact Or.inr (Or.inr ⟨L, hbad,
        a, f, g, k, ha, haEdges, hfg, hreflected, hk⟩)

theorem rlc_goodComponentContacts_of_anchoredGoodComponentContacts
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hcomponent :
      RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts
        gamma gamma' rho) :
    RlcCentralFaceFilledBoundaryGoodComponentContacts gamma gamma' rho := by
  obtain ⟨_B, x, y, _hanchor, hx, hy, hxPath, hyPath⟩ := hcomponent
  exact ⟨x, y, hx.trans hy, hxPath, hyPath⟩


theorem rlc_anchoredGoodComponentContacts_or_reachableBarrier_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts
        gamma gamma' rho ∨
      ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
        (z : Site 2),
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            B.firstFace z ∧
          rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma' := by
  classical
  let B := Classical.choice
    (rlc_centralFace_retainedAnchoredBoundary_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno)
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ :=
    rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith rho hno
  by_cases hx : (rlc_connectorCentralFaceGoodBoundaryGraph
      gamma gamma' rho).Reachable B.firstFace x
  · by_cases hy : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable B.firstFace y
    · left
      exact ⟨B, x, y, B.anchor_mem_goodBoundaryGraph hfaith,
        hx.symm, hy, hxPath, hyPath⟩
    · right
      obtain ⟨z, hz, hzBarrier⟩ :=
        rlc_goodBoundary_barrier_hit_before_first_bad
          B hfaith hySupport hy
      exact ⟨B, z, hz, hzBarrier⟩
  · right
    obtain ⟨z, hz, hzBarrier⟩ :=
      rlc_goodBoundary_barrier_hit_before_first_bad
        B hfaith hxSupport hx
    exact ⟨B, z, hz, hzBarrier⟩


theorem rlc_anchoredGoodComponentContacts_or_reachableClassifiedBarrier_of_faithful_failure
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    RlcCentralFaceFilledBoundaryAnchoredGoodComponentContacts
        gamma gamma' rho ∨
      ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
        (z : Site 2),
        (rlc_connectorCentralFaceGoodBoundaryGraph gamma gamma' rho).Reachable
            B.firstFace z ∧
          (rlc_dualReflect z ∈ rlc_pathVertices gamma.1 ∨
            rlc_dualReflect z ∈ rlc_pathVertices gamma'.1 ∨
            (0 < (rlc_dualReflect z) 0 ∧
              ∃ w ∈ rlc_pathVertices gamma'.1,
                rlc_dualReflect z = rlc_flipX w) ∨
            ((rlc_dualReflect z) 0 < 0 ∧
              ∃ w ∈ rlc_pathVertices gamma.1,
                rlc_dualReflect z = rlc_flipX w)) := by
  rcases
      rlc_anchoredGoodComponentContacts_or_reachableBarrier_of_faithful_failure
        gamma gamma' hfaith rho hno with hcontacts | ⟨B, z, hz, hzBarrier⟩
  · exact Or.inl hcontacts
  · exact Or.inr ⟨B, z, hz,
      rlc_connectorBarrier_original_or_strict_reflected
        gamma gamma' hzBarrier⟩


theorem rlc_anchorToFaithfulContacts_reachable_or_barrier
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (hno : rho ∉ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma') :
    ∃ (B : RlcCentralFaceRetainedAnchoredBoundary gamma gamma' rho)
      (x y : Site 2),
      rlc_dualReflect x ∈ rlc_pathVertices gamma.1 ∧
        rlc_dualReflect y ∈ rlc_pathVertices gamma'.1 ∧
        ((rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Reachable B.firstFace x ∨
          ∃ z : Site 2,
            (rlc_connectorCentralFaceGoodBoundaryGraph
                gamma gamma' rho).Reachable B.firstFace z ∧
              rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') ∧
        ((rlc_connectorCentralFaceGoodBoundaryGraph
            gamma gamma' rho).Reachable B.firstFace y ∨
          ∃ z : Site 2,
            (rlc_connectorCentralFaceGoodBoundaryGraph
                gamma gamma' rho).Reachable B.firstFace z ∧
              rlc_dualReflect z ∈ rlc_connectorBarrier gamma gamma') := by
  classical
  let B := Classical.choice
    (rlc_centralFace_retainedAnchoredBoundary_of_failure
      gamma gamma' hfaith.toRlcBookPositionedTracePair rho hno)
  obtain ⟨x, y, hxSupport, hySupport, hxPath, hyPath⟩ :=
    rlc_centralFaceFilledBoundaryContacts_of_faithful_failure
      gamma gamma' hfaith rho hno
  refine ⟨B, x, y, hxPath, hyPath, ?_, ?_⟩
  · by_cases hx : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable B.firstFace x
    · exact Or.inl hx
    · exact Or.inr (rlc_goodBoundary_barrier_hit_before_first_bad
        B hfaith hxSupport hx)
  · by_cases hy : (rlc_connectorCentralFaceGoodBoundaryGraph
        gamma gamma' rho).Reachable B.firstFace y
    · exact Or.inl hy
    · exact Or.inr (rlc_goodBoundary_barrier_hit_before_first_bad
        B hfaith hySupport hy)


end
end StatMech.Universality
