/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc76buffer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc75spanningtree.Part4
import Def.StatisticalMechanics.Code.Walls.bc76buffer
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc76_far_of_sameBufferResidue {L : ℕ} {y y' : Site d}
    (hres : bc76_bufferResVec L y = bc76_bufferResVec L y') (hne : y ≠ y') :
    ∃ i, 4 * L < ((y - y') i).natAbs := by
  obtain ⟨i, hi⟩ : ∃ i, y i ≠ y' i := by
    by_contra h; simp only [not_exists, not_not] at h; exact hne (funext h)
  refine ⟨i, ?_⟩
  have hposZ : (0 : ℤ) < 4 * L + 1 := by positivity
  have hresi : (y i % (4 * L + 1 : ℤ)).toNat = (y' i % (4 * L + 1 : ℤ)).toNat := by
    have := congrArg (fun f => (f i).val) hres
    simpa [bc76_bufferResVec] using this
  have hnn1 : 0 ≤ y i % (4 * L + 1 : ℤ) := Int.emod_nonneg _ (by positivity)
  have hnn2 : 0 ≤ y' i % (4 * L + 1 : ℤ) := Int.emod_nonneg _ (by positivity)
  have hemodeq : y i % (4 * L + 1 : ℤ) = y' i % (4 * L + 1 : ℤ) := by omega
  have hdvd : (4 * L + 1 : ℤ) ∣ (y - y') i := by
    rw [Pi.sub_apply]
    have hmodeq : (y i - y' i) % (4 * L + 1 : ℤ) = 0 := by
      rw [Int.sub_emod, hemodeq, sub_self, Int.zero_emod]
    exact Int.dvd_of_emod_eq_zero hmodeq
  have hnz : (y - y') i ≠ 0 := by rw [Pi.sub_apply]; exact sub_ne_zero.mpr hi
  have hdvdabs : (4 * L + 1 : ℤ) ∣ |(y - y') i| := (dvd_abs _ _).mpr hdvd
  have hge : (4 * L + 1 : ℤ) ≤ |(y - y') i| := Int.le_of_dvd (abs_pos.mpr hnz) hdvdabs
  have hge' : (4 * L + 1 : ℤ) ≤ ((y - y') i).natAbs := by rwa [Int.abs_eq_natAbs] at hge
  have : (4 * L + 1 : ℕ) ≤ ((y - y') i).natAbs := by exact_mod_cast hge'
  omega


theorem bc76_bufferFiber_boxes_disjoint {L : ℕ} {y y' : Site d}
    (hres : bc76_bufferResVec L y = bc76_bufferResVec L y') (hne : y ≠ y') :
    Disjoint (bc61_boxAround d L y) (bc61_boxAround d L y') := by
  obtain ⟨i, hi⟩ := bc76_far_of_sameBufferResidue hres hne
  exact bc64_boxAround_disjoint_of_farCoord i (by omega)


theorem bc76_bufferGap {L : ℕ} {y y' : Site d}
    (hres : bc76_bufferResVec L y = bc76_bufferResVec L y') (hne : y ≠ y') :
    ∃ i, ∀ x : Site d, ((x - y) i).natAbs ≤ L → 2 * L < ((x - y') i).natAbs := by
  obtain ⟨i, hi⟩ := bc76_far_of_sameBufferResidue hres hne
  refine ⟨i, fun x hx => ?_⟩
  
  have hsub : (y - y') i = (x - y') i - (x - y) i := by simp only [Pi.sub_apply]; ring
  have hle : ((y - y') i).natAbs ≤ ((x - y') i).natAbs + ((x - y) i).natAbs := by
    rw [hsub]; exact Int.natAbs_sub_le _ _
  omega


theorem bc76_fiberQuotEdge_lifts {ω : ConfigSpace (Sym2 (Site d))} {L R : ℕ}
    {c : Fin d → Fin (2 * L + 1)} {y s t : Site d} (hy : y ∈ bc73_fiber ω L R c)
    (hs : s ≠ y) (ht : t ≠ y) (hadj : (bc75_fiberQuot ω L R c).Adj s t) :
    ∃ p q, p ∉ bc61_boxAround d L y ∧ q ∉ bc61_boxAround d L y ∧
      bc75_collapseFiber ω L R c p = s ∧ bc75_collapseFiber ω L R c q = t ∧
      (openSubgraph d ω).Adj p q := by
  obtain ⟨_, p, q, hp, hq, hpq⟩ := hadj
  refine ⟨p, q, ?_, ?_, hp, hq, hpq⟩
  · intro hpbox
    exact hs (by rw [← hp]; exact bc75_collapseFiber_eq hy hpbox)
  · intro hqbox
    exact ht (by rw [← hq]; exact bc75_collapseFiber_eq hy hqbox)


end StatMech.Walls
