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
import Def.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFullPhysicalPermutation.Part35
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

theorem rlc_idxOf_le_of_mem_takeUntil
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b z q : V} (W : G.Walk a b)
    (hz : z ∈ W.support) (hq : q ∈ (W.takeUntil z hz).support) :
    W.support.idxOf q ≤ W.support.idxOf z := by
  have hpref := W.support_takeUntil_prefix_support hz
  have hidxEq := hpref.idxOf_eq_of_mem hq
  have hidxLt := List.idxOf_lt_length_of_mem hq
  rw [SimpleGraph.Walk.length_support,
    SimpleGraph.Walk.length_takeUntil] at hidxLt
  rw [hidxEq] at hidxLt
  omega


theorem rlc_mem_takeUntil_iff_idxOf_le
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b z q : V} (W : G.Walk a b)
    (hz : z ∈ W.support) (hq : q ∈ W.support) :
    q ∈ (W.takeUntil z hz).support ↔
      W.support.idxOf q ≤ W.support.idxOf z := by
  constructor
  · exact rlc_idxOf_le_of_mem_takeUntil W hz
  · intro hle
    rw [SimpleGraph.Walk.takeUntil_eq_take,
      SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.take_support_eq_support_take_succ,
      List.mem_take_iff_getElem]
    have hqLt : W.support.idxOf q < W.support.length :=
      List.idxOf_lt_length_of_mem hq
    refine ⟨W.support.idxOf q, ?_, ?_⟩
    · omega
    · exact List.getElem_idxOf hqLt


theorem rlc_isPath_mem_dropUntil_iff_idxOf_le
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b z q : V} (W : G.Walk a b) (hW : W.IsPath)
    (hz : z ∈ W.support) (hq : q ∈ W.support) :
    q ∈ (W.dropUntil z hz).support ↔
      W.support.idxOf z ≤ W.support.idxOf q := by
  constructor
  · exact rlc_isPath_idxOf_le_of_mem_dropUntil W hW hz
  · intro hle
    have hzLt : W.support.idxOf z < W.support.length :=
      List.idxOf_lt_length_of_mem hz
    have hzLe : W.support.idxOf z ≤ W.length := by
      rw [SimpleGraph.Walk.length_support] at hzLt
      omega
    rw [SimpleGraph.Walk.dropUntil_eq_drop,
      SimpleGraph.Walk.support_copy,
      SimpleGraph.Walk.drop_support_eq_support_drop_min,
      Nat.min_eq_left hzLe, List.mem_drop_iff_getElem]
    let j := W.support.idxOf q - W.support.idxOf z
    have hqLt : W.support.idxOf q < W.support.length :=
      List.idxOf_lt_length_of_mem hq
    have hj : W.support.idxOf z + j < W.support.length := by
      simpa [j, Nat.add_sub_of_le hle] using hqLt
    refine ⟨j, by simpa [Nat.add_comm] using hj, ?_⟩
    have hget := W.getVert_support_idxOf hq
    rw [W.getVert_eq_support_getElem
      (by rw [SimpleGraph.Walk.length_support] at hqLt; omega)] at hget
    simpa [j, Nat.add_comm, Nat.add_sub_of_le hle] using hget


theorem rlc_walk_exists_last_lower_first_upper_contact
    {V : Type*} {G : SimpleGraph V} {a b : V}
    (W : G.Walk a b) (lower upper : V → Prop)
    {i0 j0 : Nat} (hi0j0 : i0 ≤ j0) (hj0Length : j0 ≤ W.length)
    (hi0Lower : lower (W.getVert i0))
    (hj0Upper : upper (W.getVert j0)) :
    ∃ i j : Nat,
      i0 ≤ i ∧ i ≤ j ∧ j ≤ j0 ∧ j0 ≤ W.length ∧
        lower (W.getVert i) ∧ upper (W.getVert j) ∧
        (∀ k : Nat, k ≤ j0 → lower (W.getVert k) → k ≤ i) ∧
        (∀ k : Nat, i ≤ k → k ≤ j0 → upper (W.getVert k) → j ≤ k) := by
  classical
  let L : Finset Nat := (Finset.range (j0 + 1)).filter fun k =>
    lower (W.getVert k)
  have hi0L : i0 ∈ L := by
    simp [L, hi0Lower]
    omega
  obtain ⟨i, hiL, hiMax⟩ := Finset.exists_max_image L id ⟨i0, hi0L⟩
  have hiInfo := Finset.mem_filter.mp hiL
  have hiJ0 : i ≤ j0 := by
    have := Finset.mem_range.mp hiInfo.1
    omega
  have hi0i : i0 ≤ i := by
    simpa using hiMax i0 hi0L
  let U : Finset Nat := (Finset.Icc i j0).filter fun k =>
    upper (W.getVert k)
  have hj0U : j0 ∈ U := by
    simp [U, hiJ0, hj0Upper]
  obtain ⟨j, hjU, hjMin⟩ := Finset.exists_min_image U id ⟨j0, hj0U⟩
  have hjInfo := Finset.mem_filter.mp hjU
  have hij : i ≤ j := (Finset.mem_Icc.mp hjInfo.1).1
  have hjj0 : j ≤ j0 := (Finset.mem_Icc.mp hjInfo.1).2
  refine ⟨i, j, hi0i, hij, hjj0, hj0Length, hiInfo.2, hjInfo.2,
    ?_, ?_⟩
  · intro k hkj0 hkLower
    apply hiMax k
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hkLower⟩
  · intro k hik hkj0 hkUpper
    apply hjMin k
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hik, hkj0⟩, hkUpper⟩


end
end StatMech.Universality
