/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePerronContinuation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle.Part3
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part11
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sum_sixVertexSectorGap
    {N n : Nat} (x : SixVertexSector N n) (hn : 0 < n) :
    ∑ i, sixVertexSectorGap x i = N - n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [Fin.sum_univ_castSucc]
  simp only [sixVertexSectorGap]
  have hnext (i : Fin m) : i.castSucc.val + 1 < m + 1 := by
    simpa using i.isLt
  simp_rw [dif_pos (hnext _)]
  simp only [Fin.val_castSucc, Fin.val_last,
    show ¬(m + 1 < m + 1) by omega, ↓reduceDIte]
  have hcard : m + 1 ≤ N := by
    have hsub : (x : Finset (Fin N)).card ≤
        (Finset.univ : Finset (Fin N)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa [x.prop] using hsub
  have hterm (i : Fin m) :
      (((sixVertexSectorPosition x ⟨i.val + 1, hnext i⟩).val -
          (sixVertexSectorPosition x i.castSucc).val - 1 : Nat) : Int) =
        (sixVertexSectorPosition x ⟨i.val + 1, hnext i⟩).val -
          (sixVertexSectorPosition x i.castSucc).val - 1 := by
    have hidx : (⟨i.val + 1, hnext i⟩ : Fin (m + 1)) = i.succ := Fin.ext rfl
    rw [hidx]
    have hlt := (sixVertexSectorPosition x).strictMono
      (Fin.castSucc_lt_succ (i := i))
    rw [Nat.cast_sub (by omega : 1 ≤
      (sixVertexSectorPosition x i.succ).val -
        (sixVertexSectorPosition x i.castSucc).val),
      Nat.cast_sub (by omega :
        (sixVertexSectorPosition x i.castSucc).val ≤
          (sixVertexSectorPosition x i.succ).val)]
    norm_num
  have hlast (z : Fin (m + 1)) (hz : z.val = 0) :
      ((N + (sixVertexSectorPosition x z).val -
          (sixVertexSectorPosition x (Fin.last m)).val - 1 : Nat) : Int) =
        N + (sixVertexSectorPosition x z).val -
          (sixVertexSectorPosition x (Fin.last m)).val - 1 := by
    have hp := (sixVertexSectorPosition x (Fin.last m)).isLt
    push_cast
    omega
  apply Int.ofNat_inj.mp
  push_cast
  simp_rw [hterm]
  simp_rw [hlast]
  let p : Nat → Int := fun k =>
    if hk : k < m + 1 then (sixVertexSectorPosition x ⟨k, hk⟩).val else 0
  let d : Nat → Int := fun k => p (k + 1) - p k - 1
  let g : Fin m → Int := fun i =>
    (sixVertexSectorPosition x i.succ).val -
      (sixVertexSectorPosition x i.castSucc).val - 1
  change (∑ i, g i) +
      ((N : Int) + (sixVertexSectorPosition x (0 : Fin (m + 1))).val -
        (sixVertexSectorPosition x (Fin.last m)).val - 1) =
    ((N - (m + 1) : Nat) : Int)
  have hsum : (∑ i, g i) = ∑ k ∈ Finset.range m, d k := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hinext : i.val + 1 < m + 1 := by omega
    have hicur : i.val < m + 1 := by omega
    simp only [g, d, p, dif_pos hinext, dif_pos hicur]
    congr 2 <;> apply congrArg Fin.val <;> rfl
  rw [hsum]
  have htel := Finset.sum_range_sub p m
  have hp0 : p 0 = (sixVertexSectorPosition x (0 : Fin (m + 1))).val := by
    simp [p]
  have hpm : p m = (sixVertexSectorPosition x (Fin.last m)).val := by
    simp only [p, dif_pos (show m < m + 1 by omega)]
    congr 2
  simp only [d]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [htel, hp0, hpm, Nat.cast_sub hcard]
  push_cast
  ring

theorem sum_sixVertexSectorGapDefects
    {N n : Nat} (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) (hn : 0 < n) :
    ∑ i, sixVertexSectorGapDefects x i = N - 2 * n := by
  have hgap (i : Fin n) : sixVertexSectorGapDefects x i + 1 =
      sixVertexSectorGap x i := by
    rw [sixVertexSectorGapDefects, Nat.sub_add_cancel]
    exact sixVertexSectorGap_pos_of_noAdjacent x hx i
  have hcard : n ≤ N := by
    have hsub : (x : Finset (Fin N)).card ≤
        (Finset.univ : Finset (Fin N)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa [x.prop] using hsub
  have hlower : n ≤ ∑ i, sixVertexSectorGap x i := by
    calc
      n = ∑ _i : Fin n, 1 := by simp
      _ ≤ ∑ i, sixVertexSectorGap x i := by
        apply Finset.sum_le_sum
        intro i _
        exact sixVertexSectorGap_pos_of_noAdjacent x hx i
  rw [sum_sixVertexSectorGap x hn] at hlower
  have hadd : (∑ i, sixVertexSectorGapDefects x i) + n =
      ∑ i, sixVertexSectorGap x i := by
    calc
      (∑ i, sixVertexSectorGapDefects x i) + n =
          ∑ i, (sixVertexSectorGapDefects x i + 1) := by
        rw [Finset.sum_add_distrib]
        simp
      _ = ∑ i, sixVertexSectorGap x i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hgap i
  rw [sum_sixVertexSectorGap x hn] at hadd
  omega


end
end StatMech.FrontierD
