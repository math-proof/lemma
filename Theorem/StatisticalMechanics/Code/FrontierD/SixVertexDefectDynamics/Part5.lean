/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDefectDynamics.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part13
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Def.StatisticalMechanics.Code.FrontierD.SixVertexDefectDynamics.Part5
open Finset


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexDefectLowerAdvance_pos
    {n : Nat} (i j : Fin n) :
    0 < sixVertexDefectLowerAdvance i j := by
  by_cases hji : j = i <;> simp [sixVertexDefectLowerAdvance, hji]

theorem sixVertexDefectLowerAdvance_sub_one
    {n : Nat} (i j : Fin n) :
    sixVertexDefectLowerAdvance i j - 1 = if j = i then 1 else 0 := by
  by_cases hji : j = i <;> simp [sixVertexDefectLowerAdvance, hji]

theorem sixVertexDefectLowerMove_bound
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n)
    (i : Fin n) (hd : 0 < sixVertexSectorGapDefects x i)
    (hlast : (sixVertexSectorPosition x ⟨n - 1, by omega⟩).val +
      sixVertexDefectLowerAdvance i ⟨n - 1, by omega⟩ < N) :
    ∀ j, (sixVertexSectorPosition x j).val +
      sixVertexDefectLowerAdvance i j < N := by
  intro j
  by_cases hnext : j.val + 1 < n
  · have hj : (⟨j.val, by omega⟩ : Fin n) = j := Fin.ext rfl
    by_cases hji : j = i
    · subst j
      simp only [sixVertexDefectLowerAdvance, if_pos]
      rw [sixVertexSectorGapDefects, sixVertexSectorGap] at hd
      simp only [dif_pos hnext] at hd
      have hnextN := (sixVertexSectorPosition x
        ⟨i.val + 1, hnext⟩).isLt
      omega
    · rw [sixVertexDefectLowerAdvance]
      simp only [if_neg hji]
      have hgap := hx.1 j.val hnext
      rw [hj] at hgap
      have hnextN := (sixVertexSectorPosition x
        ⟨j.val + 1, hnext⟩).isLt
      omega
  · have hjlast : j = ⟨n - 1, by omega⟩ := by
      apply Fin.ext
      change j.val = n - 1
      omega
    simpa only [hjlast] using hlast

theorem sixVertexDefectLowerMove_between
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x)
    (i : Fin n) (hd : 0 < sixVertexSectorGapDefects x i)
    (k : Nat) (hk : k + 1 < n) :
    (sixVertexSectorPosition x ⟨k, by omega⟩).val +
        sixVertexDefectLowerAdvance i ⟨k, by omega⟩ <
      (sixVertexSectorPosition x ⟨k + 1, hk⟩).val := by
  by_cases hki : (⟨k, by omega⟩ : Fin n) = i
  · rw [sixVertexDefectLowerAdvance, if_pos hki]
    rw [← hki] at hd
    rw [sixVertexSectorGapDefects, sixVertexSectorGap] at hd
    simp only [dif_pos hk] at hd
    omega
  · rw [sixVertexDefectLowerAdvance]
    simp only [if_neg hki]
    exact hx.1 k hk

theorem sixVertexDefectLowerMove_mono
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x)
    (i : Fin n) (hd : 0 < sixVertexSectorGapDefects x i) :
    ∀ j k : Fin n, j < k →
      (sixVertexSectorPosition x j).val + sixVertexDefectLowerAdvance i j <
        (sixVertexSectorPosition x k).val + sixVertexDefectLowerAdvance i k := by
  intro j k hjk
  have hjnext : j.val + 1 < n := by omega
  have hbetween := sixVertexDefectLowerMove_between
    x hx i hd j.val hjnext
  have hj0 : (⟨j.val, by omega⟩ : Fin n) = j := Fin.ext rfl
  rw [hj0] at hbetween
  have hnextle :
      (sixVertexSectorPosition x ⟨j.val + 1, hjnext⟩).val ≤
        (sixVertexSectorPosition x k).val := by
    exact_mod_cast (sixVertexSectorPosition x).monotone (by
      change j.val + 1 ≤ k.val
      omega)
  have hkpos := sixVertexDefectLowerAdvance_pos i k
  omega


end
end StatMech.FrontierD
