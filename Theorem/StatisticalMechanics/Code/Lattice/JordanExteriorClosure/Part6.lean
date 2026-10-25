/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanExteriorClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Lattice.TwoPathsCrossWinding.Part2
import Def.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part6
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box


theorem jec_rayCount_vsegUp (z : Site 2) (col r : ℤ) (k : ℕ) :
    jec_rayCount z (jec_vsegUp col r k) =
      (if col ≤ z 0 - 1 ∧ r ≤ z 1 - 1 ∧ z 1 - 1 ≤ r + (k:ℤ) - 1 then 1 else 0) := by
  classical
  induction k generalizing r with
  | zero =>
    simp only [jec_vsegUp, jec_rayCount, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_nil,
      List.countP_nil]
    rw [eq_comm, if_neg]; push_cast; omega
  | succ k ih =>
    rw [jec_vsegUp, jec_rayCount, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_cons,
      List.countP_cons]
    have ihr := ih (r+1)
    rw [jec_rayCount] at ihr
    rw [ihr]
    have hhead : (decide (jec_rayEdge z s(![col, r], ![col, r+1]))) =
        decide (col ≤ z 0 - 1 ∧ r = z 1 - 1) := by
      rw [decide_eq_decide]
      simp only [jec_rayEdge_mk, Matrix.cons_val_zero, Matrix.cons_val_one, true_and]
      omega
    rw [hhead]
    simp only [decide_eq_true_eq]
    push_cast
    split_ifs <;> omega


theorem jec_rayCount_hsegRight (z : Site 2) (row t : ℤ) (k : ℕ) :
    jec_rayCount z (jec_hsegRight row t k) = 0 := by
  classical
  induction k generalizing t with
  | zero =>
    simp only [jec_hsegRight, jec_rayCount, SimpleGraph.Walk.edges_copy,
      SimpleGraph.Walk.edges_nil, List.countP_nil]
  | succ k ih =>
    rw [jec_hsegRight, jec_rayCount, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_cons,
      List.countP_cons]
    have ihr := ih (t+1)
    rw [jec_rayCount] at ihr
    rw [ihr]
    have hhead : ¬ jec_rayEdge z s(![t, row], ![t+1, row]) := by
      rw [jec_rayEdge_mk]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      omega
    rw [decide_eq_false hhead]; simp


theorem jec_vsegUp_support (col r : ℤ) (k : ℕ) {p : Site 2}
    (hp : p ∈ (jec_vsegUp col r k).support) :
    p 0 = col ∧ r ≤ p 1 ∧ p 1 ≤ r + (k:ℤ) := by
  induction k generalizing r with
  | zero =>
    rw [jec_vsegUp, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_nil] at hp
    rw [List.mem_singleton] at hp; subst hp
    refine ⟨rfl, ?_, ?_⟩ <;> simp
  | succ k ih =>
    rw [jec_vsegUp, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons,
      List.mem_cons] at hp
    rcases hp with hp | hp
    · subst hp
      refine ⟨rfl, by simp, ?_⟩
      simp only [Matrix.cons_val_one]; push_cast; omega
    · obtain ⟨h0, h1, h2⟩ := ih (r+1) hp
      refine ⟨h0, by omega, by push_cast at h2 ⊢; omega⟩


theorem jec_hsegRight_support (row t : ℤ) (k : ℕ) {p : Site 2}
    (hp : p ∈ (jec_hsegRight row t k).support) :
    p 1 = row ∧ t ≤ p 0 ∧ p 0 ≤ t + (k:ℤ) := by
  induction k generalizing t with
  | zero =>
    rw [jec_hsegRight, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_nil] at hp
    rw [List.mem_singleton] at hp; subst hp
    refine ⟨rfl, ?_, ?_⟩ <;> simp
  | succ k ih =>
    rw [jec_hsegRight, SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_cons,
      List.mem_cons] at hp
    rcases hp with hp | hp
    · subst hp
      refine ⟨rfl, by simp, ?_⟩
      simp only [Matrix.cons_val_zero]; push_cast; omega
    · obtain ⟨h1, h0a, h0b⟩ := ih (t+1) hp
      refine ⟨h1, by omega, by push_cast at h0b ⊢; omega⟩


end Lattice
end StatMech
