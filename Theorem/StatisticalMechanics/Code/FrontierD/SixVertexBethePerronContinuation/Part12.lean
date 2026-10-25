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
import Def.StatisticalMechanics.Code.FrontierD.SixVertexBethePerronContinuation.Part12
open Finset Filter Matrix Topology


namespace StatMech.FrontierD

noncomputable section

theorem sixVertexSectorAdvance_pos_of_forward_disjoint
    {N n : Nat} (x y : SixVertexSector N n)
    (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)))
    (i : Fin n) :
    0 < sixVertexSectorAdvance x y i := by
  have hpos := (sixVertexForwardInterlaced_iff_positions x y).mp hforward
  have hne : sixVertexSectorPosition x i ≠ sixVertexSectorPosition y i := by
    intro heq
    rw [Finset.disjoint_left] at hdisj
    exact hdisj (sixVertexSectorPosition_mem x i)
      (heq ▸ sixVertexSectorPosition_mem y i)
  rw [sixVertexSectorAdvance, Nat.sub_pos_iff_lt]
  exact_mod_cast lt_of_le_of_ne (hpos.1 i) hne

theorem sixVertexSectorAdvance_le_gap_of_forward_disjoint
    {N n : Nat} (x y : SixVertexSector N n)
    (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)))
    (i : Fin n) :
    sixVertexSectorAdvance x y i ≤ sixVertexSectorGap x i := by
  have hpos := (sixVertexForwardInterlaced_iff_positions x y).mp hforward
  have hne (a b : Fin n) :
      sixVertexSectorPosition x a ≠ sixVertexSectorPosition y b := by
    intro heq
    rw [Finset.disjoint_left] at hdisj
    exact hdisj (sixVertexSectorPosition_mem x a)
      (heq ▸ sixVertexSectorPosition_mem y b)
  rw [sixVertexSectorAdvance, sixVertexSectorGap]
  split_ifs with hnext
  · have hle := hpos.2 i.val hnext
    have hlt : (sixVertexSectorPosition y i).val <
        (sixVertexSectorPosition x ⟨i.val + 1, hnext⟩).val := by
      have hle' : sixVertexSectorPosition y i ≤
          sixVertexSectorPosition x ⟨i.val + 1, hnext⟩ := by
        simpa only using hle
      exact_mod_cast lt_of_le_of_ne hle' (Ne.symm (hne _ i))
    omega
  · have hyN := (sixVertexSectorPosition y i).isLt
    omega

theorem sixVertexSectorGap_transport_of_forward_disjoint
    {N n : Nat} (x y : SixVertexSector N n)
    (hforward : SixVertexForwardInterlaced (sixVertexSectorRow x)
      (sixVertexSectorRow y))
    (hdisj : Disjoint (x : Finset (Fin N)) (y : Finset (Fin N)))
    (i : Fin n) :
    sixVertexSectorGap y i + sixVertexSectorAdvance x y i =
      sixVertexSectorGap x i +
        sixVertexSectorAdvance x y (sixVertexSectorCyclicNext i) := by
  have hsupport := sixVertexSectorNoAdjacent_pair_of_forward_disjoint
    x y hforward hdisj
  have hadv (j : Fin n) :=
    sixVertexSectorAdvance_pos_of_forward_disjoint x y hforward hdisj j
  rw [sixVertexSectorGap, sixVertexSectorGap,
    sixVertexSectorAdvance, sixVertexSectorAdvance,
    sixVertexSectorCyclicNext]
  split_ifs with hnext
  · have hxi := hsupport.1.1 i.val hnext
    have hyi := hsupport.2.1 i.val hnext
    have hi : (⟨i.val, by omega⟩ : Fin n) = i := Fin.ext rfl
    rw [hi] at hxi hyi
    have hai := hadv i
    have han := hadv (⟨i.val + 1, hnext⟩ : Fin n)
    rw [sixVertexSectorAdvance, Nat.sub_pos_iff_lt] at hai han
    have hgapx :
        (sixVertexSectorPosition x ⟨i.val + 1, hnext⟩).val -
            (sixVertexSectorPosition x i).val - 1 +
            ((sixVertexSectorPosition x i).val + 1) =
          (sixVertexSectorPosition x ⟨i.val + 1, hnext⟩).val := by omega
    have hgapy :
        (sixVertexSectorPosition y ⟨i.val + 1, hnext⟩).val -
            (sixVertexSectorPosition y i).val - 1 +
            ((sixVertexSectorPosition y i).val + 1) =
          (sixVertexSectorPosition y ⟨i.val + 1, hnext⟩).val := by omega
    have hadvi :
        (sixVertexSectorPosition y i).val -
            (sixVertexSectorPosition x i).val +
            (sixVertexSectorPosition x i).val =
          (sixVertexSectorPosition y i).val := by omega
    have hadvn :
        (sixVertexSectorPosition y ⟨i.val + 1, hnext⟩).val -
            (sixVertexSectorPosition x ⟨i.val + 1, hnext⟩).val +
            (sixVertexSectorPosition x ⟨i.val + 1, hnext⟩).val =
          (sixVertexSectorPosition y ⟨i.val + 1, hnext⟩).val := by omega
    omega

  · have hn : 0 < n := Nat.pos_of_ne_zero
      (fun hn => by subst n; exact Fin.elim0 i)
    have hilast : i.val = n - 1 := by omega
    have hxwrap := hsupport.1.2 hn
    have hywrap := hsupport.2.2 hn
    have hi : (⟨n - 1, by omega⟩ : Fin n) = i := by
      apply Fin.ext
      simpa using hilast.symm
    rw [hi] at hxwrap hywrap
    have hai := hadv i
    have ha0 := hadv (⟨0, hn⟩ : Fin n)
    rw [sixVertexSectorAdvance, Nat.sub_pos_iff_lt] at hai ha0
    have hgapx :
        N + (sixVertexSectorPosition x ⟨0, hn⟩).val -
            (sixVertexSectorPosition x i).val - 1 +
            ((sixVertexSectorPosition x i).val + 1) =
          N + (sixVertexSectorPosition x ⟨0, hn⟩).val := by omega
    have hgapy :
        N + (sixVertexSectorPosition y ⟨0, hn⟩).val -
            (sixVertexSectorPosition y i).val - 1 +
            ((sixVertexSectorPosition y i).val + 1) =
          N + (sixVertexSectorPosition y ⟨0, hn⟩).val := by omega
    have hadvi :
        (sixVertexSectorPosition y i).val -
            (sixVertexSectorPosition x i).val +
            (sixVertexSectorPosition x i).val =
          (sixVertexSectorPosition y i).val := by omega
    have hadv0 :
        (sixVertexSectorPosition y ⟨0, hn⟩).val -
            (sixVertexSectorPosition x ⟨0, hn⟩).val +
            (sixVertexSectorPosition x ⟨0, hn⟩).val =
          (sixVertexSectorPosition y ⟨0, hn⟩).val := by omega
    omega


end
end StatMech.FrontierD
