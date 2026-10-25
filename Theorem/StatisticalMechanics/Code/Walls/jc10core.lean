/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc10core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarExistence.Part4
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Walls.jc10farupeven
import Theorem.StatisticalMechanics.Code.Walls.jc10localconstancy
import Theorem.StatisticalMechanics.Code.Walls.jc10cornerexists
import Theorem.StatisticalMechanics.Code.Walls.jc10cornercellinK
open Set SimpleGraph Function


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc10core_countP_or_decomp {α : Type*} (l : List α) (p q r : α → Prop) [DecidablePred p]
    [DecidablePred q] [DecidablePred r]
    (hdec : ∀ a, p a ↔ (q a ∨ r a)) (hexcl : ∀ a, ¬ (q a ∧ r a)) :
    l.countP (fun a => decide (p a)) =
      l.countP (fun a => decide (q a)) + l.countP (fun a => decide (r a)) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.countP_cons, ih]
    by_cases hq : q a <;> by_cases hr : r a
    · exact absurd ⟨hq, hr⟩ (hexcl a)
    · have hp : p a := (hdec a).mpr (Or.inl hq)
      simp only [hp, hq, hr, decide_false, if_false, Bool.false_eq_true, decide_true]
      omega
    · have hp : p a := (hdec a).mpr (Or.inr hr)
      simp only [hp, hq, hr, decide_false, if_false, Bool.false_eq_true, decide_true]
      omega
    · have hp : ¬ p a := fun h => by rcases (hdec a).mp h with h' | h' <;> [exact hq h'; exact hr h']
      simp only [hp, hq, hr, decide_false, if_false, Bool.false_eq_true]
      omega


theorem jc10core_dartFace_row_le_tail (e : Dart) : (dartFace e) 1 ≤ e.tail 1 := by
  unfold dartFace
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
  have h1 : Lattice.negPart (e.dir 1) ≤ 0 := by unfold Lattice.negPart; split_ifs <;> omega
  have h2 : Lattice.negPart (rot90Fun e.dir 1) ≤ 0 := by unfold Lattice.negPart; split_ifs <;> omega
  omega


theorem jc10core_support_row_le (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (c : Site 2) (hc : IsExtremeCell K c) (p : Site 2)
    (hp : p ∈ (mpl_orbitLoop K a).support) : p 1 ≤ c 1 := by
  rw [mpl_orbitLoop_support, mpl_orbitFaceLoop, SimpleGraph.Walk.support_copy,
    dartOrbitFaceWalk_support, List.mem_map] at hp
  obtain ⟨k, _, hk⟩ := hp
  subst hk
  have htail : ((dartNext K)^[k] a.1).tail ∈ K :=
    (iterate_isBoundaryDart K a.1 a.2 k).tail_mem
  have hrow : (dartFace ((dartNext K)^[k] a.1)) 1 ≤ ((dartNext K)^[k] a.1).tail 1 :=
    jc10core_dartFace_row_le_tail _
  by_contra hcon
  push Not at hcon
  exact extremeCell_not_mem_of_higher K c _ hc (by omega) htail


theorem jc10core_colPt_off_support (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (c : Site 2) (hc : IsExtremeCell K c) (j : ℤ) (hj : c 1 < j) :
    (![c 0, j] : Site 2) ∉ (mpl_orbitLoop K a).support := by
  intro hmem
  have := jc10core_support_row_le K a c hc _ hmem
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one] at this
  omega


theorem jc10core_col_parity_const (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (c : Site 2) (hc : IsExtremeCell K c) (n : ℕ) :
    (Even (jec_rayCount (![c 0, c 1 + 1 + (n : ℤ)] : Site 2) (mpl_orbitLoop K a)) ↔
      Even (jec_rayCount (![c 0, c 1 + 1] : Site 2) (mpl_orbitLoop K a))) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hadj : (hypercubicLattice 2).Adj (![c 0, c 1 + 1 + (m : ℤ)] : Site 2)
        (![c 0, c 1 + 1 + (m : ℤ) + 1] : Site 2) := by
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      norm_num
    have hu : (![c 0, c 1 + 1 + (m : ℤ)] : Site 2) ∉ (mpl_orbitLoop K a).support :=
      jc10core_colPt_off_support K a c hc _ (by omega)
    have hv : (![c 0, c 1 + 1 + (m : ℤ) + 1] : Site 2) ∉ (mpl_orbitLoop K a).support :=
      jc10core_colPt_off_support K a c hc _ (by omega)
    have hstep := jc10_localConstancy (mpl_orbitLoop K a) hadj hu hv
    have hcast : c 1 + 1 + ((m : ℤ) + 1) = c 1 + 1 + (m : ℤ) + 1 := by ring
    rw [Nat.cast_succ, hcast, ← hstep]; exact ih


theorem jc10core_above_even (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (c : Site 2) (hc : IsExtremeCell K c) :
    Even (jec_rayCount (![c 0, c 1 + 1] : Site 2) (mpl_orbitLoop K a)) := by
  
  obtain ⟨R, hR⟩ := jc10_orbitLoop_box_confined K a
  
  set N : ℕ := ((R : ℤ) + 1 - c 1).toNat + 1 with hN
  have hbig : (R : ℤ) < c 1 + 1 + (N : ℤ) := by
    have h2 : ((R : ℤ) + 1 - c 1) ≤ ((R : ℤ) + 1 - c 1).toNat := Int.self_le_toNat _
    push_cast [hN]
    omega
  
  have hfar : Even (jec_rayCount (![c 0, c 1 + 1 + (N : ℤ)] : Site 2) (mpl_orbitLoop K a)) := by
    refine jc10_farUp_even (mpl_orbitLoop K a) R hR (![c 0, c 1 + 1 + (N : ℤ)] : Site 2) ?_
    simpa using hbig
  exact (jc10core_col_parity_const K a c hc N).mp hfar


end Walls
end StatMech
