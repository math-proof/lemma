/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFullPhysicalPermutation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
import Theorem.StatisticalMechanics.Code.Lattice.CollaredWalkCrossing
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFaithfulExclusive.Part2
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part38
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_bookShiftedOuterTrace_bridge_endpoints_mem {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1) :
    rlc_dualReflect.symm z ∈
        (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support ∧
      rlc_dualReflect.symm (rlc_flipX z) ∈
        (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support := by
  let WR := rlc_ambientCrossingWalk gamma.1
  let WL := rlc_ambientCrossingWalk gamma'.1
  have hzWR : z ∈ WR.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 z).2 hzRight
  have hzWL : rlc_flipX z ∈ WL.support :=
    (rlc_mem_ambientCrossingWalk_support_iff_pathVertices
      gamma'.1 (rlc_flipX z)).2 hzLeft
  let rightOuter := WR.dropUntil z hzWR
  let leftOuter := WL.takeUntil (rlc_flipX z) hzWL
  have hmiddleStart : (![(-z 0 - 1), z 1 - 1] : Site 2) =
      rlc_dualReflect.symm z := by
    ext i
    fin_cases i <;> simp
  have hmiddleEnd : (![(z 0 - 1), z 1 - 1] : Site 2) =
      rlc_dualReflect.symm (rlc_flipX z) := by
    ext i
    fin_cases i <;> simp [rlc_flipX, rlc_flipXFun]
  let middle : (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm z)
      (rlc_dualReflect.symm (rlc_flipX z)) :=
    (sw_horizSeg (z 1 - 1) (-z 0 - 1) (z 0 - 1)).copy
      hmiddleStart hmiddleEnd
  let core := (((rightOuter.map
    rlc_dualReflectSymmLatticeHom).reverse.append middle).append
      (leftOuter.map rlc_dualReflectSymmLatticeHom).reverse)
  let q : Site 2 := rlc_dualReflect.symm (gamma'.1.1 : Site 2)
  have hqCoord : (![q 0, q 1] : Site 2) = q := by
    ext i
    fin_cases i <;> simp
  let extension : (hypercubicLattice 2).Walk q ![2 * n, q 1] :=
    (sw_horizSeg (q 1) (q 0) (2 * n)).copy hqCoord rfl
  change rlc_dualReflect.symm z ∈ (core.append extension).support ∧
    rlc_dualReflect.symm (rlc_flipX z) ∈ (core.append extension).support
  constructor
  · rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    change rlc_dualReflect.symm z ∈
      (((rightOuter.map rlc_dualReflectSymmLatticeHom).reverse.append
        middle).append
          (leftOuter.map rlc_dualReflectSymmLatticeHom).reverse).support
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inr middle.start_mem_support)
  · rw [SimpleGraph.Walk.mem_support_append_iff]
    left
    change rlc_dualReflect.symm (rlc_flipX z) ∈
      (((rightOuter.map rlc_dualReflectSymmLatticeHom).reverse.append
        middle).append
          (leftOuter.map rlc_dualReflectSymmLatticeHom).reverse).support
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inr middle.end_mem_support)


theorem rlc_bookShiftedOuterTrace_forced_contacts_mem_orderedArc {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y z : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxEq : rlc_dualReflect x = z)
    (hyEq : rlc_dualReflect y = rlc_flipX z) :
    (x ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support ∧
        x ∈ (rlc_orderedContourArc c hx hy).support) ∧
      (y ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support ∧
        y ∈ (rlc_orderedContourArc c hx hy).support) := by
  have hbridge := rlc_bookShiftedOuterTrace_bridge_endpoints_mem
    gamma gamma' hzRight hzLeft
  have hxBridge : rlc_dualReflect.symm z = x := by
    rw [← hxEq]
    exact rlc_dualReflect.symm_apply_apply x
  have hyBridge : rlc_dualReflect.symm (rlc_flipX z) = y := by
    rw [← hyEq]
    exact rlc_dualReflect.symm_apply_apply y
  exact ⟨⟨by simpa [hxBridge] using hbridge.1,
      (rlc_orderedContourArc c hx hy).start_mem_support⟩,
    ⟨by simpa [hyBridge] using hbridge.2,
      (rlc_orderedContourArc c hx hy).end_mem_support⟩⟩


theorem rlc_bookShiftedOuterTrace_forced_contacts_distinct {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {omega : RlcTwoChannelEdgeConfig gamma gamma'}
    {u x y z : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hx : x ∈ c.support) (hy : y ∈ c.support)
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxEq : rlc_dualReflect x = z)
    (hyEq : rlc_dualReflect y = rlc_flipX z) :
    ((x ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support ∧
          x ∈ (rlc_orderedContourArc c hx hy).support) ∧
        (y ∈ (rlc_bookShiftedOuterTrace gamma gamma' hzRight hzLeft).support ∧
          y ∈ (rlc_orderedContourArc c hx hy).support)) ∧
      x ≠ y := by
  refine ⟨rlc_bookShiftedOuterTrace_forced_contacts_mem_orderedArc
      c hx hy hzRight hzLeft hxEq hyEq, ?_⟩
  intro hxy
  apply hfaith.intersection_ne_flip hzRight hzLeft
  exact hxEq.symm.trans ((congrArg rlc_dualReflect hxy).trans hyEq)


end
end StatMech.Universality
