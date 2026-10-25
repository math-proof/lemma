/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGraph.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann.Part6
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.IsingSusceptibilityPlus.Part2
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalSimonMass
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness StatMech.Lattice

open StatMech.Percolation

variable {d k R : Nat}

theorem isingSiteToDyadicTorus_injectiveOn_box
    (hside : 2 * R < isingDyadicSide k) :
    Set.InjOn (isingSiteToDyadicTorus k) (box d R) := by
  intro x hx y hy hxy
  funext i
  have hi := congrFun hxy i
  change ((x i : Int) : ZMod (2 ^ (k + 2))) = (y i : Int) at hi
  have hdvd : ((2 ^ (k + 2) : Nat) : Int) ∣ y i - x i :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub
      (x i) (y i) (2 ^ (k + 2))).mp hi
  have hnat : (y i - x i).natAbs ≤ 2 * R := by
    calc
      (y i - x i).natAbs ≤ (y i).natAbs + (x i).natAbs :=
        Int.natAbs_sub_le _ _
      _ ≤ R + R := Nat.add_le_add (hy i) (hx i)
      _ = 2 * R := by omega
  have habs : |y i - x i| < (isingDyadicSide k : Int) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hnat.trans_lt hside
  have hzero : y i - x i = 0 :=
    Int.eq_zero_of_abs_lt_dvd hdvd habs
  omega

theorem isingSiteToDyadicTorus_injectiveOn_finset
    (S : Finset (Site d)) (hS : ↑S ⊆ box d R)
    (hside : 2 * R < isingDyadicSide k) :
    Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)) :=
  (isingSiteToDyadicTorus_injectiveOn_box hside).mono hS

theorem isingSiteToDyadicTorus_coordShift
    (x : Site d) (i : Fin d) (b : Bool) :
    isingSiteToDyadicTorus k (coordShift x i (stepSign b)) =
      if b then
        isingSiteToDyadicTorus k x + isingTorusStep i
      else
        isingSiteToDyadicTorus k x - isingTorusStep i := by
  funext j
  by_cases hij : j = i
  · subst j
    cases b
    · simp [isingSiteToDyadicTorus, coordShift, stepSign, isingTorusStep,
        sub_eq_add_neg]
      have hm : ((-1 : Int) : ZMod (2 ^ (k + 2))) = -1 := by
        rw [show (-1 : Int) = -(1 : Int) by norm_num,
          Int.cast_neg, Int.cast_one]
      rw [← hm]
      exact Int.cast_add (R := ZMod (2 ^ (k + 2))) (x i) (-1)
    · simp [isingSiteToDyadicTorus, coordShift, stepSign, isingTorusStep,
        sub_eq_add_neg]
      simpa only [Int.cast_one] using
        (Int.cast_add (R := ZMod (2 ^ (k + 2))) (x i) 1)
  · cases b <;>
      simp [isingSiteToDyadicTorus, coordShift, stepSign, isingTorusStep,
        hij, sub_eq_add_neg]

theorem isingSiteToDyadicTorus_map_adj
    {x y : Site d} (hxy : (hypercubicLattice d).Adj x y) :
    (isingTorusGraph d k).Adj
      (isingSiteToDyadicTorus k x) (isingSiteToDyadicTorus k y) := by
  obtain ⟨i, b, rfl⟩ := adj_exists_dir hxy
  rw [isingTorusGraph_adj_iff, isingSiteToDyadicTorus_coordShift]
  by_cases hb : b
  · exact ⟨i, Or.inl (if_pos hb)⟩
  · refine ⟨i, Or.inr ?_⟩
    rw [if_neg hb]
    abel

theorem coordShift_mem_box_succ {x : Site d} (hx : x ∈ box d R)
    (i : Fin d) (b : Bool) :
    coordShift x i (stepSign b) ∈ box d (R + 1) := by
  intro j
  by_cases hji : j = i
  · subst j
    simp only [coordShift, Function.update_self, stepSign]
    have hxi := hx i
    cases b
    · have h := Int.natAbs_sub_le (x i) 1
      norm_num at h
      exact h.trans (by omega)
    · have h := Int.natAbs_add_le (x i) 1
      norm_num at h
      exact h.trans (by omega)
  · rw [coordShift, Function.update_of_ne hji]
    exact (hx j).trans (Nat.le_succ R)

theorem isingSiteToDyadicTorus_reflects_adj_on_box
    {x y : Site d} (hx : x ∈ box d R) (hy : y ∈ box d R)
    (hside : 2 * (R + 1) < isingDyadicSide k)
    (hxy : (isingTorusGraph d k).Adj
      (isingSiteToDyadicTorus k x) (isingSiteToDyadicTorus k y)) :
    (hypercubicLattice d).Adj x y := by
  rw [isingTorusGraph_adj_iff] at hxy
  rcases hxy with ⟨i, h | h⟩
  · let z := coordShift x i (stepSign true)
    have hz : z ∈ box d (R + 1) := coordShift_mem_box_succ hx i true
    have hy' : y ∈ box d (R + 1) := box_mono d (Nat.le_succ R) hy
    have hcast : isingSiteToDyadicTorus k y =
        isingSiteToDyadicTorus k z := by
      rw [h, isingSiteToDyadicTorus_coordShift]
      simp [z]
    have hyz : y = z :=
      isingSiteToDyadicTorus_injectiveOn_box hside hy' hz hcast
    rw [hyz]
    exact adj_coordShift x i true
  · let z := coordShift y i (stepSign true)
    have hz : z ∈ box d (R + 1) := coordShift_mem_box_succ hy i true
    have hx' : x ∈ box d (R + 1) := box_mono d (Nat.le_succ R) hx
    have hcast : isingSiteToDyadicTorus k x =
        isingSiteToDyadicTorus k z := by
      rw [h, isingSiteToDyadicTorus_coordShift]
      simp [z]
    have hxz : x = z :=
      isingSiteToDyadicTorus_injectiveOn_box hside hx' hz hcast
    rw [hxz]
    exact (adj_coordShift y i true).symm


end StatMech.FrontierA
