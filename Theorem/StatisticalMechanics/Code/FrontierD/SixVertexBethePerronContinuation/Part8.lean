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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part8
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem sixVertexCyclicSuccEquiv_val
    {N : Nat} (hN : 0 < N) (i : Fin N) :
    (sixVertexCyclicSuccEquiv hN i).val = (i.val + 1) % N := by
  simp [sixVertexCyclicSuccEquiv, Equiv.addRight, Fin.add_def]


theorem sixVertexSector_disjoint_cyclicSucc_of_noAdjacent
    {N n : Nat} (hN : 0 < N) (x : SixVertexSector N n)
    (hx : SixVertexSectorNoAdjacent x) :
    Disjoint (x : Finset (Fin N))
      ((x : Finset (Fin N)).map (sixVertexCyclicSuccEquiv hN).toEmbedding) := by
  rw [Finset.disjoint_left]
  intro z hzx hzsucc
  rw [Finset.mem_map] at hzsucc
  obtain ⟨w, hwx, hwz⟩ := hzsucc
  have hzi : z ∈ Set.range (sixVertexSectorPosition x) :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem x z).mpr hzx
  have hwj : w ∈ Set.range (sixVertexSectorPosition x) :=
    (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem x w).mpr hwx
  obtain ⟨i, hi⟩ := hzi
  obtain ⟨j, hj⟩ := hwj
  have heq : sixVertexSectorPosition x i =
      sixVertexCyclicSuccEquiv hN (sixVertexSectorPosition x j) := by
    calc
      sixVertexSectorPosition x i = z := hi
      _ = sixVertexCyclicSuccEquiv hN w := hwz.symm
      _ = sixVertexCyclicSuccEquiv hN (sixVertexSectorPosition x j) := by
        rw [hj]
  have hval := congrArg Fin.val heq
  rw [sixVertexCyclicSuccEquiv_val] at hval
  by_cases hjlast : (sixVertexSectorPosition x j).val + 1 < N
  · rw [Nat.mod_eq_of_lt hjlast] at hval
    have hji : j < i := by
      apply (sixVertexSectorPosition x).lt_iff_lt.mp
      exact_mod_cast (show (sixVertexSectorPosition x j).val <
        (sixVertexSectorPosition x i).val by omega)
    have hijval : i.val = j.val + 1 := by
      by_contra hne
      have hskip : j.val + 1 < i.val := by omega
      let j' : Fin n := ⟨j.val + 1, lt_of_lt_of_le hskip i.isLt.le⟩
      have hjj' : j < j' := by
        change j.val < (j' : Fin n).val
        simp only [j', Fin.val_mk]
        omega
      have hj'i : j' < i := by
        change (j' : Fin n).val < i.val
        simpa only [j', Fin.val_mk] using hskip
      have hpos1 := (sixVertexSectorPosition x).strictMono hjj'
      have hpos2 := (sixVertexSectorPosition x).strictMono hj'i
      have hpos1' : (sixVertexSectorPosition x j).val <
          (sixVertexSectorPosition x j').val := by exact_mod_cast hpos1
      have hpos2' : (sixVertexSectorPosition x j').val <
          (sixVertexSectorPosition x i).val := by exact_mod_cast hpos2
      omega
    have hgap := hx.1 j.val (by omega)
    have hindex : (⟨j.val + 1, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      simpa using hijval.symm
    have hgap' : (sixVertexSectorPosition x j).val + 1 <
        (sixVertexSectorPosition x i).val := by
      have hjindex : (⟨j.val, by omega⟩ : Fin n) = j := Fin.ext rfl
      rw [hjindex, hindex] at hgap
      exact hgap
    omega
  · have hjval : (sixVertexSectorPosition x j).val = N - 1 := by
      have hjle := (sixVertexSectorPosition x j).isLt
      omega
    have hval0 : (sixVertexSectorPosition x i).val = 0 := by
      rw [hjval] at hval
      have hpred : N - 1 + 1 = N := by omega
      rw [hpred, Nat.mod_self] at hval
      exact hval
    have hival : i.val = 0 := by
      by_contra hi0
      let i0 : Fin n := ⟨0, Nat.pos_of_ne_zero (fun hn0 => by
        subst n
        exact Fin.elim0 i)⟩
      have hi0lt : i0 < i := by
        change (i0 : Fin n).val < i.val
        simpa only [i0, Fin.val_mk] using Nat.pos_of_ne_zero hi0
      have hpos := (sixVertexSectorPosition x).strictMono hi0lt
      have hpos' : (sixVertexSectorPosition x i0).val <
          (sixVertexSectorPosition x i).val := by exact_mod_cast hpos
      omega
    have hjindex : j.val = n - 1 := by
      by_contra hjne
      have hjsucc : j.val + 1 < n := by omega
      let j' : Fin n := ⟨j.val + 1, hjsucc⟩
      have hpos := (sixVertexSectorPosition x).strictMono
        (show j < j' by
          change j.val < (j' : Fin n).val
          simp only [j', Fin.val_mk]
          omega)
      have hpos' : (sixVertexSectorPosition x j).val <
          (sixVertexSectorPosition x j').val := by exact_mod_cast hpos
      have hj'N := (sixVertexSectorPosition x j').isLt
      omega
    have hn : 0 < n := Nat.pos_of_ne_zero (fun hn0 => by
      subst n
      exact Fin.elim0 i)
    have hwrap := hx.2 hn
    have hiindex : (⟨0, hn⟩ : Fin n) = i := by
      apply Fin.ext
      simpa using hival.symm
    have hjindex' : (⟨n - 1, by omega⟩ : Fin n) = j := by
      apply Fin.ext
      simpa using hjindex.symm
    rw [hiindex, hjindex', hval0, hjval] at hwrap
    omega


end
end StatMech.FrontierD
