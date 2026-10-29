/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal
open Finset

set_option linter.deprecated false
set_option linter.style.longLine false


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem cylinder_all_open (p : NNReal) (hp : p ≤ 1) (F : Finset (Sym2 (Site d))) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp)
      ((F : Set (Sym2 (Site d))).pi (fun _ => ({true} : Set Bool)))
      = (p : ENNReal) ^ F.card := by
  have key := Measure.infinitePi_pi (μ := fun _ : Sym2 (Site d) => bernoulliMeasure p hp)
    (s := F) (t := fun _ => ({true} : Set Bool)) (fun i _ => measurableSet_singleton _)
  rw [bernoulliProductMeasure, key]
  simp only [bernoulliMeasure_apply_true]
  rw [Finset.prod_const]


theorem adj_coordShift (x : Site d) (i : Fin d) (b : Bool) :
    (hypercubicLattice d).Adj x (coordShift x i (stepSign b)) := by
  rw [hypercubicLattice_adj, Finset.sum_eq_single i]
  · simp only [coordShift, Function.update_self, stepSign]; cases b <;> simp
  · intro j _ hj; rw [coordShift, Function.update_of_ne hj, sub_self, Int.natAbs_zero]
  · intro h; exact absurd (Finset.mem_univ i) h


theorem adj_exists_dir {x y : Site d} (h : (hypercubicLattice d).Adj x y) :
    ∃ (i : Fin d) (b : Bool), y = coordShift x i (stepSign b) := by
  rw [hypercubicLattice_adj] at h
  classical
  set f : Fin d → ℕ := fun i => (x i - y i).natAbs with hf
  have hsum : ∑ i, f i = 1 := h
  have hne : ∃ i, f i ≠ 0 := by
    by_contra hc
    push Not at hc
    simp only [hc, Finset.sum_const_zero] at hsum
    exact one_ne_zero hsum.symm
  obtain ⟨i, _⟩ := hne
  have hfi1 : f i = 1 := by
    have hle : f i ≤ ∑ j, f j :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hsum] at hle; omega
  have hothers : ∀ j ≠ i, f j = 0 := by
    intro j hj
    have hpair : f i + f j ≤ ∑ k, f k := by
      have := Finset.sum_le_sum_of_subset (s := {i, j}) (f := f) (Finset.subset_univ _)
      rw [Finset.sum_pair hj.symm] at this; omega
    rw [hsum] at hpair; omega
  rw [hf] at hfi1
  have hpm : x i - y i = 1 ∨ x i - y i = -1 := by
    rcases Int.natAbs_eq_iff.mp hfi1 with h1 | h1 <;> [left; right] <;> omega
  refine ⟨i, decide (y i = x i + 1), ?_⟩
  funext k
  by_cases hk : k = i
  · subst hk
    simp only [coordShift, Function.update_self, stepSign]
    rcases hpm with h1 | h1
    · have : y k = x k - 1 := by omega
      have hdec : decide (y k = x k + 1) = false := by apply decide_eq_false; omega
      rw [hdec]; simp; omega
    · have : y k = x k + 1 := by omega
      have hdec : decide (y k = x k + 1) = true := by apply decide_eq_true; omega
      rw [hdec]; simp; omega
  · have hfk : f k = 0 := hothers k hk
    rw [hf] at hfk
    have : x k = y k := by have := Int.natAbs_eq_zero.mp hfk; omega
    rw [coordShift, Function.update_of_ne hk]; omega


theorem l1_getVert_le {ω : ConfigSpace (Sym2 (Site d))} {v : Site d}
    (q : (openSubgraph d ω).Walk (origin d) v) (k : ℕ) :
    (∑ i, (q.getVert k i).natAbs) ≤ k := by
  induction k with
  | zero => simp [Walk.getVert_zero, origin]
  | succ k ih =>
    by_cases hk : k < q.length
    · have hadj : (hypercubicLattice d).Adj (q.getVert k) (q.getVert (k + 1)) :=
        openSubgraph_le ω (q.adj_getVert_succ hk)
      rw [hypercubicLattice_adj] at hadj
      have hstep : (∑ i, (q.getVert (k + 1) i - q.getVert k i).natAbs) = 1 := by
        rw [show (∑ i, (q.getVert (k + 1) i - q.getVert k i).natAbs)
              = ∑ i, (q.getVert k i - q.getVert (k + 1) i).natAbs from ?_, hadj]
        apply Finset.sum_congr rfl; intro i _
        rw [← Int.natAbs_neg, neg_sub]
      calc ∑ i, (q.getVert (k + 1) i).natAbs
          ≤ ∑ i, ((q.getVert (k + 1) i - q.getVert k i).natAbs + (q.getVert k i).natAbs) := by
            apply Finset.sum_le_sum; intro i _
            have hle := Int.natAbs_add_le (q.getVert (k + 1) i - q.getVert k i) (q.getVert k i)
            rwa [sub_add_cancel] at hle
        _ = (∑ i, (q.getVert (k + 1) i - q.getVert k i).natAbs) + ∑ i, (q.getVert k i).natAbs := by
            rw [Finset.sum_add_distrib]
        _ ≤ 1 + k := Nat.add_le_add (le_of_eq hstep) ih
        _ = k + 1 := by ring
    · push Not at hk
      have h1 : q.getVert (k + 1) = q.getVert k := by
        rw [q.getVert_of_length_le hk, q.getVert_of_length_le (by omega)]
      rw [h1]; exact le_trans ih (Nat.le_succ k)


end Percolation
end StatMech
