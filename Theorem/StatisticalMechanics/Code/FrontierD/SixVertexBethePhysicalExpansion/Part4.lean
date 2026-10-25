/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalExpansion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalReduction.Part2
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalExpansion.Part4
open Finset Matrix


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBetheConstrainedTuples_eq_piFinset
    {n : Nat} (N : Nat) (x : Fin (n + 1) -> Int)
    (S : Finset (Fin (n + 1))) (hS : SixVertexBetheNoAdjacent S)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i ≤ x i) :
    (sixVertexBetheCyclicIntervalTuples N x).filter
        (fun q => S ⊆ sixVertexBetheCollisionSet N x q) =
      Fintype.piFinset (sixVertexBetheConstrainedCoordinateSet N x S) := by
  classical
  ext q
  simp only [Finset.mem_filter, mem_sixVertexBetheCyclicIntervalTuples,
    Fintype.mem_piFinset]
  constructor
  · rintro ⟨hq, hcollision⟩ i
    by_cases hi : i ∈ S
    · simp only [sixVertexBetheConstrainedCoordinateSet, hi, if_true,
        Finset.mem_singleton]
      exact (mem_sixVertexBetheCollisionSet N x q i).mp (hcollision hi) |>.1
    · by_cases hpred : (finRotate (n + 1)).symm i ∈ S
      · simp only [sixVertexBetheConstrainedCoordinateSet, hi, if_false,
          hpred, if_true, Finset.mem_singleton]
        have hmem := hcollision hpred
        have hcol := (mem_sixVertexBetheCollisionSet N x q _).mp hmem
        simpa using hcol.2
      · simp only [sixVertexBetheConstrainedCoordinateSet, hi, if_false,
          hpred, Finset.mem_Icc]
        exact hq i
  · intro hq
    constructor
    · intro i
      have hi := hq i
      by_cases his : i ∈ S
      · simp only [sixVertexBetheConstrainedCoordinateSet, his, if_true,
          Finset.mem_singleton] at hi
        rw [hi]
        exact ⟨hgap i, le_rfl⟩
      · by_cases hpred : (finRotate (n + 1)).symm i ∈ S
        · simp only [sixVertexBetheConstrainedCoordinateSet, his, if_false,
            hpred, if_true, Finset.mem_singleton] at hi
          rw [hi]
          exact ⟨le_rfl, hgap i⟩
        · unfold sixVertexBetheConstrainedCoordinateSet at hi
          rw [if_neg his, if_neg hpred] at hi
          simpa using hi
    · intro i hi
      rw [mem_sixVertexBetheCollisionSet]
      constructor
      · have hqi := hq i
        simpa [sixVertexBetheConstrainedCoordinateSet, hi] using hqi
      · have hnext_not : finRotate (n + 1) i ∉ S := hS i hi
        have hqnext := hq (finRotate (n + 1) i)
        simp only [sixVertexBetheConstrainedCoordinateSet, hnext_not,
          if_false] at hqnext
        have hpred :
            (finRotate (n + 1)).symm (finRotate (n + 1) i) ∈ S := by
          simpa using hi
        simp only [hpred, if_true, Finset.mem_singleton] at hqnext
        exact hqnext


theorem sixVertexBethe_geometricInterval_int
    (c : Real) {z : Complex} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    {a b : Int} (hab : a < b) :
    z ^ a + (c : Complex) ^ 2 * (∑ y ∈ Finset.Ioo a b, z ^ y) + z ^ b =
      sixVertexBetheL c z * z ^ a + sixVertexBetheM c z * z ^ b := by
  let motive : ∀ b : Int, a + 1 ≤ b -> Prop := fun b _ =>
    z ^ a + (c : Complex) ^ 2 * (∑ y ∈ Finset.Ioo a b, z ^ y) + z ^ b =
      sixVertexBetheL c z * z ^ a + sixVertexBetheM c z * z ^ b
  have hbase : motive (a + 1) le_rfl := by
    dsimp [motive]
    have hempty : Finset.Ioo a (a + 1) = ∅ := by
      rw [Finset.Ioo_add_one_right_eq_Ioc, Finset.Ioc_self]
    rw [hempty]
    simp only [Finset.sum_empty, mul_zero, add_zero]
    rw [zpow_add_one₀ hz0]
    unfold sixVertexBetheL sixVertexBetheM
    field_simp [sub_ne_zero.mpr (Ne.symm hz1)]
    ring
  have hstep : ∀ (b : Int) (hb : a + 1 ≤ b), motive b hb ->
      motive (b + 1) (by omega) := by
    intro b hb ih
    have hab' : a < b := by omega
    dsimp [motive] at ih ⊢
    rw [Finset.Ioo_add_one_right_eq_Ioc,
      ← Finset.Ioo_insert_right hab', Finset.sum_insert]
    · rw [zpow_add_one₀ hz0]
      calc
        z ^ a + (c : Complex) ^ 2 *
              (z ^ b + ∑ x ∈ Finset.Ioo a b, z ^ x) + z ^ b * z =
            (z ^ a + (c : Complex) ^ 2 *
              (∑ x ∈ Finset.Ioo a b, z ^ x) + z ^ b) +
              (c : Complex) ^ 2 * z ^ b - z ^ b + z ^ b * z := by ring
        _ = (sixVertexBetheL c z * z ^ a +
              sixVertexBetheM c z * z ^ b) +
              (c : Complex) ^ 2 * z ^ b - z ^ b + z ^ b * z := by rw [ih]
        _ = sixVertexBetheL c z * z ^ a +
              sixVertexBetheM c z * (z ^ b * z) := by
          unfold sixVertexBetheM
          field_simp [sub_ne_zero.mpr (Ne.symm hz1)]
          ring
    · simp
  exact Int.leInduction hbase hstep b (by omega)


theorem sixVertexBethe_intervalLocalSum
    (c : Real) {z : Complex} (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    {a b : Int} (hab : a < b) :
    (∑ y ∈ Finset.Icc a b,
      (if y = a \/ y = b then 1 else (c : Complex) ^ 2) * z ^ y) =
      sixVertexBetheL c z * z ^ a + sixVertexBetheM c z * z ^ b := by
  have hIcc : Finset.Icc a b =
      insert a (insert b (Finset.Ioo a b)) := by
    ext y
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioo]
    omega
  rw [hIcc, Finset.sum_insert, Finset.sum_insert]
  · simp only [true_or, if_true, or_true]
    have hinter :
        (∑ y ∈ Finset.Ioo a b,
          (if y = a \/ y = b then 1 else (c : Complex) ^ 2) * z ^ y) =
          (c : Complex) ^ 2 * ∑ y ∈ Finset.Ioo a b, z ^ y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      have hy' := Finset.mem_Ioo.mp hy
      rw [if_neg (by omega)]
    rw [hinter]
    convert sixVertexBethe_geometricInterval_int c hz0 hz1 hab using 1 <;> ring
  · simp
  · simp only [Finset.mem_insert, Finset.mem_Ioo, not_or]
    exact ⟨hab.ne, by omega⟩


theorem sixVertexBetheCollisionConstrainedIntervalSum_eq_prod
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (hS : SixVertexBetheNoAdjacent S)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i ≤ x i) :
    sixVertexBetheCollisionConstrainedIntervalSum N c z x S =
      ∏ i, ∑ y ∈ sixVertexBetheConstrainedCoordinateSet N x S i,
        (if y = sixVertexBetheShiftCoordinates N x i \/ y = x i
          then 1 else (c : Complex) ^ 2) * z i ^ y := by
  classical
  unfold sixVertexBetheCollisionConstrainedIntervalSum
    sixVertexBetheIntervalTupleWeight
  rw [sixVertexBetheConstrainedTuples_eq_piFinset N x S hS hgap]
  exact (Finset.prod_univ_sum
    (sixVertexBetheConstrainedCoordinateSet N x S)
    (fun i y =>
      (if y = sixVertexBetheShiftCoordinates N x i \/ y = x i
        then 1 else (c : Complex) ^ 2) * z i ^ y)).symm


theorem sixVertexBetheCollisionConstrainedIntervalSum_eq_LMprod
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (hS : SixVertexBetheNoAdjacent S)
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
    (hz0 : ∀ i, z i ≠ 0) (hz1 : ∀ i, z i ≠ 1) :
    sixVertexBetheCollisionConstrainedIntervalSum N c z x S =
      ∏ i, if i ∈ S then z i ^ x i
        else if (finRotate (n + 1)).symm i ∈ S then
          z i ^ (sixVertexBetheShiftCoordinates N x i)
        else
          sixVertexBetheL c (z i) *
              z i ^ (sixVertexBetheShiftCoordinates N x i) +
            sixVertexBetheM c (z i) * z i ^ x i := by
  rw [sixVertexBetheCollisionConstrainedIntervalSum_eq_prod N c z x S hS
    (fun i => (hgap i).le)]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i ∈ S
  · simp [sixVertexBetheConstrainedCoordinateSet, hi]
  · by_cases hpred : (finRotate (n + 1)).symm i ∈ S
    · have hpred' : i - 1 ∈ S := by simpa using hpred
      simp [sixVertexBetheConstrainedCoordinateSet, hi, hpred']
    · simp only [sixVertexBetheConstrainedCoordinateSet, hi, if_false,
        hpred]
      exact sixVertexBethe_intervalLocalSum c (hz0 i) (hz1 i) (hgap i)

theorem sixVertexBetheCollisionConstrainedIntervalSum_eq_zero
    {n : Nat} (N : Nat) (c : Real) (z : Fin (n + 1) -> Complex)
    (x : Fin (n + 1) -> Int) (S : Finset (Fin (n + 1)))
    (hgap : ∀ i, sixVertexBetheShiftCoordinates N x i < x i)
    (hS : ¬ SixVertexBetheNoAdjacent S) :
    sixVertexBetheCollisionConstrainedIntervalSum N c z x S = 0 := by
  classical
  simp only [SixVertexBetheNoAdjacent, not_forall] at hS
  obtain ⟨i, hi⟩ := hS
  simp only [Classical.not_imp, not_not] at hi
  unfold sixVertexBetheCollisionConstrainedIntervalSum
  apply Finset.sum_eq_zero
  intro q hq
  have hsubset := (Finset.mem_filter.mp hq).2
  have hcoli := (mem_sixVertexBetheCollisionSet N x q i).mp
    (hsubset hi.1)
  have hcolnext := (mem_sixVertexBetheCollisionSet N x q
    (finRotate (n + 1) i)).mp (hsubset hi.2)
  exfalso
  exact (hgap (finRotate (n + 1) i)).ne
    (hcoli.2.symm.trans hcolnext.1)


end
end StatMech.FrontierD
