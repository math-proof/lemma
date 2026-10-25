/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardFinitePolygonEar.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPolygonTurning.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardFourSignMajority
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardHalfPlaneSegment
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardInteriorSideSplice
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAntipodalExclusion
import Mathlib.Data.List.Rotate
import Def.StatisticalMechanics.Code.FrontierA.KacWardFinitePolygonEar.Part3


namespace StatMech.FrontierA

@[simp] theorem kwRemoveVertexOne_zero {n : ℕ} [NeZero n]
    (vertex : Fin (n + 1) → ℂ) :
    kwRemoveVertexOne vertex 0 = vertex 0 := by
  simp [kwRemoveVertexOne]

@[simp] theorem kwRemoveVertexOne_one {n : ℕ} [NeZero n]
    (hn : 2 ≤ n) (vertex : Fin (n + 1) → ℂ) :
    kwRemoveVertexOne vertex 1 = vertex 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  simp [kwRemoveVertexOne]

@[simp] theorem kwRemoveVertexOne_succ_fixed
    {m : ℕ} (vertex : Fin (m + 3) → ℂ) (i : Fin (m + 1)) :
    kwRemoveVertexOne vertex i.succ = vertex i.succ.succ := by
  simp [kwRemoveVertexOne]


theorem kwCyclicEdgeVector_removeVertexOne_zero
    {n : ℕ} [NeZero n] (hn : 2 ≤ n)
    (vertex : Fin (n + 1) → ℂ) :
    kwCyclicEdgeVector (kwRemoveVertexOne vertex) 0 =
      kwCyclicEdgeVector vertex 0 + kwCyclicEdgeVector vertex 1 := by
  unfold kwCyclicEdgeVector
  have hnew : (0 : Fin n) + 1 = 1 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  have hold0 : (0 : Fin (n + 1)) + 1 = 1 := by
    apply Fin.ext
    simp
  have hold1 : (1 : Fin (n + 1)) + 1 = 2 := by
    apply Fin.ext
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 2 < n + 1)]
  rw [hnew, hold0, hold1]
  rw [kwRemoveVertexOne_zero, kwRemoveVertexOne_one hn]
  ring


theorem kwCyclicEdgeVector_removeVertexOne_succ
    {m : ℕ} (vertex : Fin (m + 3) → ℂ) (i : Fin (m + 1)) :
    kwCyclicEdgeVector (kwRemoveVertexOne vertex) i.succ =
      kwCyclicEdgeVector vertex i.succ.succ := by
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [kwCyclicEdgeVector, kwRemoveVertexOne]
    congr 1
  · simp [kwCyclicEdgeVector, kwRemoveVertexOne]
    have hlt : (1 : Fin (m + 3)) < (j.castSucc.succ + 1).succ := by
      change 1 < (j.castSucc.succ + 1).val + 1
      have hj := j.isLt
      have hnowrap : j.val + 2 < m + 2 := by omega
      simp [Fin.val_add, Nat.mod_eq_of_lt hnowrap]
    rw [Fin.succAbove_of_lt_succ _ _ hlt]
    congr 1
    apply Fin.ext
    have hj := j.isLt
    have hnew : (j.castSucc.succ).val + 1 < m + 2 := by
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    have hold : (j.castSucc.succ.succ).val + 1 < m + 3 := by
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    rw [Fin.val_succ, Fin.val_add_one_of_lt' hnew,
      Fin.val_add_one_of_lt' hold]
    simp

@[simp] theorem kwRemoveVertexOne_succ_add_one
    {m : ℕ} (vertex : Fin (m + 3) → ℂ) (i : Fin (m + 1)) :
    kwRemoveVertexOne vertex (i.succ + 1) =
      vertex (i.succ.succ + 1) := by
  have hedge := kwCyclicEdgeVector_removeVertexOne_succ vertex i
  unfold kwCyclicEdgeVector at hedge
  rw [kwRemoveVertexOne_succ_fixed] at hedge
  linear_combination hedge


theorem kwCyclicEdgeList_removeVertexOne
    {m : ℕ} (vertex : Fin (m + 3) → ℂ) :
    kwCyclicEdgeList (kwRemoveVertexOne vertex) =
      (kwCyclicEdgeVector vertex 0 + kwCyclicEdgeVector vertex 1) ::
        List.ofFn (fun i : Fin (m + 1) ↦
          kwCyclicEdgeVector vertex i.succ.succ) := by
  unfold kwCyclicEdgeList
  rw [List.ofFn_succ]
  congr 1
  · exact kwCyclicEdgeVector_removeVertexOne_zero (by omega) vertex
  · congr 1
    funext i
    exact kwCyclicEdgeVector_removeVertexOne_succ vertex i


theorem kwCyclicEdgeList_eq_first_two
    {m : ℕ} (vertex : Fin (m + 3) → ℂ) :
    kwCyclicEdgeList vertex =
      kwCyclicEdgeVector vertex 0 :: kwCyclicEdgeVector vertex 1 ::
        List.ofFn (fun i : Fin (m + 1) ↦
          kwCyclicEdgeVector vertex i.succ.succ) := by
  unfold kwCyclicEdgeList
  rw [List.ofFn_succ, List.ofFn_succ]
  congr 2


end StatMech.FrontierA
