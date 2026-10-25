/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/OffClusterIndep.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.LastExit.Part2
open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


section AbstractWalk

variable {V : Type*} {G : SimpleGraph V}


theorem firstExitIndex {a b : V} (p : G.Walk a b) (D : Set V) [DecidablePred (· ∈ D)]
    (hb : b ∉ D) :
    ∃ j, j ≤ p.length ∧ p.getVert j ∉ D ∧ ∀ i, i < j → p.getVert i ∈ D := by
  classical
  set Tt : Finset ℕ := (Finset.range (p.length + 1)).filter (fun n => p.getVert n ∉ D) with hT
  have hLmem : p.length ∈ Tt := by
    rw [hT]; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [p.getVert_length]; exact hb⟩
  have hTne : Tt.Nonempty := ⟨p.length, hLmem⟩
  set j := Tt.min' hTne with hj
  have hjT : j ∈ Tt := Tt.min'_mem hTne
  rw [hT] at hjT
  simp only [Finset.mem_filter, Finset.mem_range] at hjT
  obtain ⟨hjle, hjD⟩ := hjT
  refine ⟨j, by omega, hjD, ?_⟩
  intro i hij
  by_contra hiD
  have hiT : i ∈ Tt := by
    rw [hT]; simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hiD⟩
  have := Tt.min'_le i hiT
  rw [← hj] at this; omega


theorem take_support_sub {a b : V} (p : G.Walk a b) (D : Set V) {j : ℕ}
    (hbefore : ∀ i, i < j → p.getVert i ∈ D) :
    ∀ z ∈ (p.take j).support, z ∈ D ∨ z = p.getVert j := by
  intro z hz
  rw [Walk.mem_support_iff_exists_getVert] at hz
  obtain ⟨k, hk, hkle⟩ := hz
  rw [Walk.take_getVert] at hk
  rw [Walk.take_length] at hkle
  by_cases hkj : k < j
  · left; rw [show min j k = k from by omega] at hk; rw [← hk]; exact hbefore k hkj
  · right; rw [show min j k = j from by omega] at hk; exact hk.symm


theorem exists_firstExit_induce {a b : V} (p : G.Walk a b) (D T : Set V)
    [DecidablePred (· ∈ D)] (ha : a ∈ T) (hb : b ∉ D)
    (hDinT : ∀ i, p.getVert i ∈ D → p.getVert i ∈ T)
    (hstep : ∀ i, i < p.length → p.getVert i ∈ D → p.getVert (i + 1) ∈ T) :
    ∃ (w : V) (hwT : w ∈ T), w ∉ D ∧
      Nonempty ((G.induce T).Walk ⟨a, ha⟩ ⟨w, hwT⟩) := by
  classical
  obtain ⟨j, hjle, hjD, hbefore⟩ := firstExitIndex p D hb
  have hwT : p.getVert j ∈ T := by
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · rw [hj0, p.getVert_zero]; exact ha
    · have hprev : p.getVert (j - 1) ∈ D := hbefore (j - 1) (by omega)
      have hjlt : j - 1 < p.length := by omega
      have := hstep (j - 1) hjlt hprev
      rwa [show j - 1 + 1 = j from by omega] at this
  have hsupp : ∀ z ∈ (p.take j).support, z ∈ T := by
    intro z hz
    rcases take_support_sub p D hbefore z hz with hzD | hzeq
    · have hzmem := hz
      rw [Walk.mem_support_iff_exists_getVert] at hzmem
      obtain ⟨k, hk, _⟩ := hzmem
      rw [Walk.take_getVert] at hk
      rw [← hk]; exact hDinT (min j k) (hk ▸ hzD)
    · rw [hzeq]; exact hwT
  refine ⟨p.getVert j, hwT, hjD, ⟨?_⟩⟩
  exact ((p.take j).induce T hsupp).copy rfl rfl

end AbstractWalk


variable {d : ℕ}


theorem adj_box_step {m : ℕ} {x z : Site d} (hx : x ∈ box d m)
    (hadj : (hypercubicLattice d).Adj x z) : z ∈ box d (m + 1) := by
  rw [hypercubicLattice_adj] at hadj
  intro i
  have hxi : (x i).natAbs ≤ m := hx i
  have hdiff : (z i - x i).natAbs ≤ 1 := by
    have hle : (z i - x i).natAbs ≤ ∑ j, (x j - z j).natAbs := by
      have hcongr : (∑ j, (x j - z j).natAbs) = ∑ j, (z j - x j).natAbs := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Int.natAbs_neg, neg_sub]
      rw [hcongr]
      exact Finset.single_le_sum (f := fun j => (z j - x j).natAbs)
        (by intros; positivity) (Finset.mem_univ i)
    omega
  have htri : (z i).natAbs ≤ (x i).natAbs + (z i - x i).natAbs := by
    have heq : z i = x i + (z i - x i) := by ring
    calc (z i).natAbs = (x i + (z i - x i)).natAbs := by rw [← heq]
      _ ≤ (x i).natAbs + (z i - x i).natAbs := Int.natAbs_add_le _ _
  omega


end Percolation
end StatMech
