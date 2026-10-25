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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part39
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_bookShiftedInnerTrace_contacts {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {z x y : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support) :
    x ∈ (rlc_bookShiftedInnerTrace gamma gamma' right flipLeft).support ∧
      y ∈ (rlc_bookShiftedInnerTrace gamma gamma' right flipLeft).support := by
  let inner := rlc_bookShiftedInnerTrace gamma gamma' right flipLeft
  have hxRight : rlc_dualReflect x ∈ right.support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hxOrder
    obtain ⟨w, hw, hwx⟩ := hxOrder
    have hwEq : w = rlc_dualReflect x := by
      apply rlc_flipX.injective
      exact hwx
    simpa [hwEq] using hw
  have hxMapped : x ∈
      (right.map rlc_dualReflectSymmLatticeHom).support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    refine ⟨rlc_dualReflect x, hxRight, ?_⟩
    change rlc_dualReflect.symm (rlc_dualReflect x) = x
    exact rlc_dualReflect.symm_apply_apply x
  have hyMapped : y ∈
      (flipLeft.map rlc_doubleDualShiftLatticeHom).support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    refine ⟨rlc_flipX (rlc_dualReflect y), hyOrder, ?_⟩
    change phb_doubleDualShift (rlc_flipX (rlc_dualReflect y)) = y
    rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm]
    exact rlc_dualReflect.symm_apply_apply y
  constructor
  · change x ∈ (((right.map rlc_dualReflectSymmLatticeHom).append _).append
      (flipLeft.map rlc_doubleDualShiftLatticeHom)).support
    rw [SimpleGraph.Walk.mem_support_append_iff,
      SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inl (Or.inl hxMapped)
  · change y ∈ (((right.map rlc_dualReflectSymmLatticeHom).append _).append
      (flipLeft.map rlc_doubleDualShiftLatticeHom)).support
    rw [SimpleGraph.Walk.mem_support_append_iff]
    exact Or.inr hyMapped


theorem rlc_bookShiftedInnerTrace_contact_indices {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (hfaith : RlcBookFaithfulTracePair gamma gamma')
    {z x y : Site 2}
    (right : (hypercubicLattice 2).Walk (gamma.1.1 : Site 2) z)
    (flipLeft : (hypercubicLattice 2).Walk z (gamma'.1.2.1 : Site 2))
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hxOrder : rlc_flipX (rlc_dualReflect x) ∈
      (right.map rlc_flipXLatticeHom).support)
    (hyOrder : rlc_flipX (rlc_dualReflect y) ∈ flipLeft.support) :
    ∃ i j : Nat,
      i ≤ j ∧
        j ≤ (rlc_bookShiftedInnerTrace gamma gamma' right flipLeft).length ∧
        (rlc_bookShiftedInnerTrace gamma gamma' right flipLeft).getVert i = x ∧
        (rlc_bookShiftedInnerTrace gamma gamma' right flipLeft).getVert j = y := by
  let P := right.map rlc_dualReflectSymmLatticeHom
  let Q := flipLeft.map rlc_doubleDualShiftLatticeHom
  have hxRight : rlc_dualReflect x ∈ right.support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hxOrder
    obtain ⟨w, hw, hwx⟩ := hxOrder
    have hwEq : w = rlc_dualReflect x := by
      apply rlc_flipX.injective
      exact hwx
    simpa [hwEq] using hw
  have hxP : x ∈ P.support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    refine ⟨rlc_dualReflect x, hxRight, ?_⟩
    exact rlc_dualReflect.symm_apply_apply x
  have hyQ : y ∈ Q.support := by
    rw [SimpleGraph.Walk.support_map, List.mem_map]
    refine ⟨rlc_flipX (rlc_dualReflect y), hyOrder, ?_⟩
    change phb_doubleDualShift (rlc_flipX (rlc_dualReflect y)) = y
    rw [rlc_doubleDualShift_flipX_eq_dualReflect_symm]
    exact rlc_dualReflect.symm_apply_apply y
  obtain ⟨i, hi, hiLen⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hxP
  obtain ⟨j, hj, hjLen⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hyQ
  have hmiddleStart : (![(-z 0 - 1), z 1 - 1] : Site 2) =
      rlc_dualReflect.symm z := by
    ext k
    fin_cases k <;> simp
  have hmiddleEnd : (![(z 0 - 1), z 1 - 1] : Site 2) =
      phb_doubleDualShift z := by
    ext k
    fin_cases k <;> simp [phb_doubleDualShift]
  let M : (hypercubicLattice 2).Walk
      (rlc_dualReflect.symm z) (phb_doubleDualShift z) :=
    (sw_horizSeg (z 1 - 1) (-z 0 - 1) (z 0 - 1)).copy
      hmiddleStart hmiddleEnd
  have hMEnds : rlc_dualReflect.symm z ≠ phb_doubleDualShift z := by
    intro heq
    have h0 := congrArg (fun w : Site 2 => w 0) heq
    simp only [rlc_dualReflect_symm_zero, phb_doubleDualShift,
      Matrix.cons_val_zero] at h0
    have hzPos := hfaith.intersection_positive hzRight hzLeft
    omega
  have hMPos : 0 < M.length := by
    rw [← SimpleGraph.Walk.not_nil_iff_lt_length]
    exact M.not_nil_of_ne hMEnds
  let j0 := (P.append M).length + j
  have hiPrefix : i < (P.append M).length := by
    calc
      i ≤ P.length := hiLen
      _ < P.length + M.length := Nat.lt_add_of_pos_right hMPos
      _ = (P.append M).length := (SimpleGraph.Walk.length_append P M).symm
  have hInnerI :
      (rlc_bookShiftedInnerTrace gamma gamma' right flipLeft).getVert i = x := by
    change ((P.append M).append Q).getVert i = x
    rw [SimpleGraph.Walk.getVert_append, if_pos hiPrefix,
      SimpleGraph.Walk.getVert_append]
    by_cases hiLt : i < P.length
    · rw [if_pos hiLt]
      exact hi
    · rw [if_neg hiLt]
      have hiEq : i = P.length := by omega
      subst i
      simpa using hi
  have hInnerJ :
      (rlc_bookShiftedInnerTrace gamma gamma' right flipLeft).getVert j0 = y := by
    change ((P.append M).append Q).getVert j0 = y
    rw [SimpleGraph.Walk.getVert_append, if_neg (by simp [j0]),
      show j0 - (P.append M).length = j by simp [j0]]
    exact hj
  refine ⟨i, j0, ?_, ?_, hInnerI, hInnerJ⟩
  · dsimp only [j0]
    have hiP : i ≤ P.length := hiLen
    omega
  · change j0 ≤ ((P.append M).append Q).length
    simp only [j0, SimpleGraph.Walk.length_append]
    exact Nat.add_le_add_left hjLen _


theorem rlc_bookShiftedOuterCoreTrace_mem_faceBox {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z v : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hv : v ∈ (rlc_bookShiftedOuterCoreTrace
      gamma gamma' hzRight hzLeft).support) :
    v ∈ rect (-2 * n - 1) (2 * n) (-n - 1) n := by
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
  change v ∈ ((((rightOuter.map rlc_dualReflectSymmLatticeHom).reverse.append
    middle).append
      (leftOuter.map rlc_dualReflectSymmLatticeHom).reverse).support) at hv
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with (hvRight | hvMiddle) | hvLeft
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse,
      SimpleGraph.Walk.support_map, List.mem_map] at hvRight
    obtain ⟨w, hw, rfl⟩ := hvRight
    change rlc_dualReflect.symm w ∈
      rect (-2 * n - 1) (2 * n) (-n - 1) n
    have hwWR : w ∈ WR.support := WR.support_dropUntil_subset hzWR hw
    have hwPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 w).1 hwWR
    have hwBox := rlc_pathVertex_mem_rect gamma.1 hwPath
    rw [mem_rect] at hwBox ⊢
    simp only [rlc_dualReflect_symm_zero, rlc_dualReflect_symm_one]
    omega
  · change v ∈ ((sw_horizSeg (z 1 - 1) (-z 0 - 1)
      (z 0 - 1)).copy hmiddleStart hmiddleEnd).support at hvMiddle
    rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hvMiddle
    obtain ⟨t, ht, rfl⟩ := hvMiddle
    have hzBox := rlc_pathVertex_mem_rect gamma.1 hzRight
    rw [Set.mem_uIcc] at ht
    rw [mem_rect] at hzBox ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rcases ht with ht | ht <;> omega
  · have hvLeft' : v ∈
        (leftOuter.map rlc_dualReflectSymmLatticeHom).support := by
      have hrev : v ∈
          (leftOuter.map rlc_dualReflectSymmLatticeHom).support.reverse :=
        (congrArg (fun l => v ∈ l)
          (SimpleGraph.Walk.support_reverse
            (leftOuter.map rlc_dualReflectSymmLatticeHom))).mp hvLeft
      exact List.mem_reverse.mp hrev
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hvLeft'
    obtain ⟨w, hw, rfl⟩ := hvLeft'
    change rlc_dualReflect.symm w ∈
      rect (-2 * n - 1) (2 * n) (-n - 1) n
    have hwWL : w ∈ WL.support := WL.support_takeUntil_subset_support hzWL hw
    have hwPath :=
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 w).1 hwWL
    have hwBox := rlc_pathVertex_mem_rect gamma'.1 hwPath
    rw [mem_rect] at hwBox ⊢
    simp only [rlc_dualReflect_symm_zero, rlc_dualReflect_symm_one]
    omega


theorem rlc_bookShiftedOuterTrace_mem_faceBox {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z v : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hv : v ∈ (rlc_bookShiftedOuterTrace
      gamma gamma' hzRight hzLeft).support) :
    v ∈ rect (-2 * n - 1) (2 * n) (-n - 1) n := by
  let core := rlc_bookShiftedOuterCoreTrace gamma gamma' hzRight hzLeft
  let q : Site 2 := rlc_dualReflect.symm (gamma'.1.1 : Site 2)
  have hqCoord : (![q 0, q 1] : Site 2) = q := by
    ext i
    fin_cases i <;> simp
  let extension : (hypercubicLattice 2).Walk q ![2 * n, q 1] :=
    (sw_horizSeg (q 1) (q 0) (2 * n)).copy hqCoord rfl
  change v ∈ (core.append extension).support at hv
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hvCore | hvExtension
  · exact rlc_bookShiftedOuterCoreTrace_mem_faceBox
      gamma gamma' hzRight hzLeft hvCore
  · change v ∈ ((sw_horizSeg (q 1) (q 0) (2 * n)).copy
      hqCoord rfl).support at hvExtension
    rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hvExtension
    obtain ⟨t, ht, rfl⟩ := hvExtension
    have hqBox := rlc_pathVertex_mem_rect gamma'.1
      (rlc_path_start_mem_vertices gamma'.1)
    have hq0 : q 0 = 2 * n - 1 := by
      simp [q, gamma'.1.1.2.2]
    rw [Set.mem_uIcc] at ht
    rw [mem_rect] at hqBox ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    simp only [q, rlc_dualReflect_symm_one] at hqBox ⊢
    rcases ht with ht | ht <;> omega


theorem rlc_bookShiftedOuterTrace_support_cases {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    {z v : Site 2}
    (hzRight : z ∈ rlc_pathVertices gamma.1)
    (hzLeft : rlc_flipX z ∈ rlc_pathVertices gamma'.1)
    (hv : v ∈ (rlc_bookShiftedOuterTrace
      gamma gamma' hzRight hzLeft).support) :
    (∃ w ∈ rlc_pathVertices gamma.1,
        v = rlc_dualReflect.symm w) ∨
      (∃ t : Int, t ∈ Set.uIcc (-z 0 - 1) (z 0 - 1) ∧
        v = ![t, z 1 - 1]) ∨
      (∃ w ∈ rlc_pathVertices gamma'.1,
        v = rlc_dualReflect.symm w) ∨
      ∃ t : Int,
        t ∈ Set.uIcc
          ((rlc_dualReflect.symm (gamma'.1.1 : Site 2)) 0) (2 * n) ∧
        v = ![t, (rlc_dualReflect.symm (gamma'.1.1 : Site 2)) 1] := by
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
  let q : Site 2 := rlc_dualReflect.symm (gamma'.1.1 : Site 2)
  have hqCoord : (![q 0, q 1] : Site 2) = q := by
    ext i
    fin_cases i <;> simp
  let extension : (hypercubicLattice 2).Walk q ![2 * n, q 1] :=
    (sw_horizSeg (q 1) (q 0) (2 * n)).copy hqCoord rfl
  change v ∈ (((((rightOuter.map
      rlc_dualReflectSymmLatticeHom).reverse.append middle).append
        (leftOuter.map rlc_dualReflectSymmLatticeHom).reverse).append
          extension).support) at hv
  rw [SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with ((hvRight | hvMiddle) | hvLeft) | hvExtension
  · rw [SimpleGraph.Walk.support_reverse, List.mem_reverse,
      SimpleGraph.Walk.support_map, List.mem_map] at hvRight
    obtain ⟨w, hw, rfl⟩ := hvRight
    have hwWR : w ∈ WR.support := WR.support_dropUntil_subset hzWR hw
    exact Or.inl ⟨w,
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma.1 w).1
        hwWR, rfl⟩
  · change v ∈ ((sw_horizSeg (z 1 - 1) (-z 0 - 1)
      (z 0 - 1)).copy hmiddleStart hmiddleEnd).support at hvMiddle
    rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hvMiddle
    exact Or.inr (Or.inl hvMiddle)
  · have hvLeft' : v ∈
        (leftOuter.map rlc_dualReflectSymmLatticeHom).support := by
      have hrev : v ∈
          (leftOuter.map rlc_dualReflectSymmLatticeHom).support.reverse :=
        (congrArg (fun l => v ∈ l)
          (SimpleGraph.Walk.support_reverse
            (leftOuter.map rlc_dualReflectSymmLatticeHom))).mp hvLeft
      exact List.mem_reverse.mp hrev
    rw [SimpleGraph.Walk.support_map, List.mem_map] at hvLeft'
    obtain ⟨w, hw, rfl⟩ := hvLeft'
    have hwWL : w ∈ WL.support := WL.support_takeUntil_subset_support hzWL hw
    exact Or.inr (Or.inr (Or.inl ⟨w,
      (rlc_mem_ambientCrossingWalk_support_iff_pathVertices gamma'.1 w).1
        hwWL, rfl⟩))
  · change v ∈ ((sw_horizSeg (q 1) (q 0) (2 * n)).copy
      hqCoord rfl).support at hvExtension
    rw [SimpleGraph.Walk.support_copy, sw_horizSeg_mem_support] at hvExtension
    simpa [q] using Or.inr (Or.inr (Or.inr hvExtension))


theorem rlc_bookShiftedOuterTrace_start_left {n : Int}
    (gamma : RlcRightDiagonalPath n) :
    (rlc_dualReflect.symm (gamma.1.2.1 : Site 2)) 0 = -2 * n - 1 := by
  rw [rlc_dualReflect_symm_zero]
  have hright : ((gamma.1.2.1 : Site 2) 0) = 2 * n := gamma.1.2.1.2.2
  omega


theorem rlc_twoChannelFullPhysical_filledBoundaryCycle_mem_faceBox
    {n : Int} (hn : 0 < n)
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (omega : RlcTwoChannelEdgeConfig gamma gamma')
    {u v : Site 2}
    (c : (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).Walk u u)
    (hcycle : c.IsCycle) (hv : v ∈ c.support) :
    v ∈ rect (-2 * n - 1) (2 * n) (-n - 1) n := by
  have hcNotNil : ¬c.Nil := by
    intro hnil
    exact hcycle.ne_nil hnil.eq_nil
  have huSupport : u ∈ (faceBoundaryGraph
      (rlc_twoChannelFullFilledReachSet gamma gamma' omega)).support :=
    (c.adj_snd hcNotNil).mem_support_left
  have hvRef := rlc_twoChannelFullFilledBoundaryWalk_reflect_mem_outerBox
    hn gamma gamma' omega c huSupport hv
  rw [rlc_twoChannelFullOuterBox, mem_rect] at hvRef
  rw [mem_rect]
  simp only [rlc_dualReflect_zero, rlc_dualReflect_one] at hvRef
  omega


end
end StatMech.Universality
