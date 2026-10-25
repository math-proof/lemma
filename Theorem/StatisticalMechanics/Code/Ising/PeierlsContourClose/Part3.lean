/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PeierlsContourClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.PeierlsUncond.Part11
import Def.StatisticalMechanics.Code.Ising.PeierlsContourClose.Part2
open MeasureTheory Filter Topology Finset SimpleGraph
open scoped BigOperators ENNReal


namespace StatMech

namespace Ising

open StatMech.Lattice

attribute [local instance] Classical.propDecidable

variable {d : ℕ}


lemma pcc_rayS_zero (c : Fin d) : pcc_rayS c 0 = origin d := by
  funext i; unfold pcc_rayS origin; simp


lemma pcc_rayS_mem_box_le (c : Fin d) (j m : ℕ) (h : j ≤ m) : pcc_rayS c j ∈ box d m := by
  intro i; unfold pcc_rayS; by_cases hh : i = c <;> simp [hh]; omega


lemma pcc_rayS_succ_not_mem_box (c : Fin d) (n : ℕ) : pcc_rayS c (n+1) ∉ box d n := by
  intro hmem; have := hmem c; unfold pcc_rayS at this; simp at this; omega


lemma pcc_rayS_adj (c : Fin d) (j : ℕ) :
    (hypercubicLattice d).Adj (pcc_rayS c j) (pcc_rayS c (j+1)) := by
  rw [hypercubicLattice_adj]
  rw [show (∑ i, ((pcc_rayS c j) i - (pcc_rayS c (j+1)) i).natAbs)
      = ∑ i : Fin d, (if i = c then (1:ℕ) else 0) from ?_]
  · rw [Finset.sum_ite_eq' Finset.univ c (fun _ => (1:ℕ))]; simp [Finset.mem_univ]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    unfold pcc_rayS; by_cases h : i = c
    · subst h; simp
    · simp [h]


lemma pcc_rayEdge_mem_bondFinsetTouch (n : ℕ) (c : Fin d) (j : ℕ) (hj : j ≤ n) :
    s(pcc_rayS c j, pcc_rayS c (j+1)) ∈ bondFinsetTouch d n := by
  unfold bondFinsetTouch
  rw [Finset.mem_image]
  refine ⟨(pcc_rayS c j, pcc_rayS c (j+1)), ?_, rfl⟩
  unfold bondPairsTouch
  rw [Finset.mem_filter, Finset.mem_product]
  refine ⟨⟨?_, ?_⟩, pcc_rayS_adj c j, Or.inl ?_⟩
  · rw [mem_boxFinset]; exact pcc_rayS_mem_box_le c j (n+1) (by omega)
  · rw [mem_boxFinset]; exact pcc_rayS_mem_box_le c (j+1) (n+1) (by omega)
  · exact pcc_rayS_mem_box_le c j n hj


lemma pcc_one_le_contourLen {n : ℕ} (hd : 1 ≤ d) {K : Finset (Site d)}
    (hKbox : (↑K : Set (Site d)) ⊆ box d n) (hoK : origin d ∈ K) :
    1 ≤ contourLen (↑K) (bondFinsetTouch d n) := by
  classical
  set c : Fin d := ⟨0, hd⟩ with hc
  set P : ℕ → Prop := fun j => pcc_rayS c j ∈ (↑K : Set (Site d)) with hP
  have hP0 : P 0 := by rw [hP]; dsimp only; rw [pcc_rayS_zero]; exact hoK
  have hPn1 : ¬ P (n+1) := by
    rw [hP]; dsimp only
    intro hmem
    exact pcc_rayS_succ_not_mem_box c n (hKbox hmem)
  have hexit : ∃ j, j ≤ n ∧ P j ∧ ¬ P (j+1) := by
    by_contra hcon
    push Not at hcon
    have key : ∀ k, k ≤ n + 1 → P k := by
      intro k
      induction k with
      | zero => intro _; exact hP0
      | succ i ih => intro hle; exact hcon i (by omega) (ih (by omega))
    exact hPn1 (key (n+1) (le_refl _))
  obtain ⟨j, hjn, hPj, hPj1⟩ := hexit
  have hcross : s(pcc_rayS c j, pcc_rayS c (j+1)) ∈ crossEdges (↑K) (bondFinsetTouch d n) := by
    unfold crossEdges
    rw [Finset.mem_filter]
    refine ⟨pcc_rayEdge_mem_bondFinsetTouch n c j hjn, ?_⟩
    rw [crosses_mk]
    constructor
    · intro _ hmem; exact hPj1 hmem
    · intro _; rw [hP] at hPj; exact hPj
  rw [contourLen, Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, ← Ne,
      ← Finset.nonempty_iff_ne_empty]
  exact ⟨_, hcross⟩


end Ising
end StatMech
