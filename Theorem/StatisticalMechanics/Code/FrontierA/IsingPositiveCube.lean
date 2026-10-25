/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingPositiveCube.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusBlockQuantitative
import Theorem.StatisticalMechanics.Code.FrontierA.IsingMessagerMiracleInfinite
import Def.StatisticalMechanics.Code.FrontierA.IsingPositiveCube
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Lattice

variable {d m k : Nat}


theorem isingPositiveCube_card (d m : Nat) :
    (isingPositiveCube d m).card = m ^ d := by
  simp [isingPositiveCube, Fintype.card_fun]

theorem isingPositiveCube_subset_box (d m : Nat) :
    (isingPositiveCube d m : Set (Site d)) ⊆ box d m := by
  intro x hx i
  have hx' : x ∈ isingPositiveCube d m := hx
  rw [isingPositiveCube, Finset.mem_map] at hx'
  obtain ⟨a, _, rfl⟩ := hx'
  change (a i).val <= m
  exact (a i).isLt.le

theorem isingPositiveCube_nonempty (d m : Nat) (hm : 1 <= m) :
    (isingPositiveCube d m).Nonempty := by
  apply Finset.card_pos.mp
  rw [isingPositiveCube_card]
  positivity

theorem isingPositiveCube_difference_l1_le
    {a b : Site d} (ha : a ∈ isingPositiveCube d m)
    (hb : b ∈ isingPositiveCube d m) :
    (∑ i, (b i - a i).natAbs) <= d * m := by
  rw [isingPositiveCube, Finset.mem_map] at ha hb
  obtain ⟨u, _, rfl⟩ := ha
  obtain ⟨v, _, rfl⟩ := hb
  calc
    (∑ i, (((v i : Nat) : Int) - ((u i : Nat) : Int)).natAbs) <=
        ∑ _i : Fin d, m := by
      apply Finset.sum_le_sum
      intro i _
      have hu : (u i).val < m := (u i).isLt
      have hv : (v i).val < m := (v i).isLt
      omega
    _ = d * m := by simp [mul_comm]

theorem isingPositiveCube_difference_mem_box
    {a b : Site d} (ha : a ∈ isingPositiveCube d m)
    (hb : b ∈ isingPositiveCube d m) : b - a ∈ box d m := by
  rw [isingPositiveCube, Finset.mem_map] at ha hb
  obtain ⟨u, _, rfl⟩ := ha
  obtain ⟨v, _, rfl⟩ := hb
  intro i
  have hu : (u i).val < m := (u i).isLt
  have hv : (v i).val < m := (v i).isLt
  have huEq : isingPositiveCubeEmbedding d m u i = ((u i).val : Int) := rfl
  have hvEq : isingPositiveCubeEmbedding d m v i = ((v i).val : Int) := rfl
  rw [Pi.sub_apply, huEq, hvEq]
  omega


end StatMech.FrontierA
