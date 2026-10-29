/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Sharpness.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
open MeasureTheory Set Filter Finset SimpleGraph
open scoped NNReal ENNReal Topology


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem finset_subset_box_su (S : Finset (Site d)) :
    ∃ N : ℕ, (S : Set (Site d)) ⊆ box d N := by
  classical
  refine ⟨S.sup (fun x => Finset.univ.sup (fun i => (x i).natAbs)), ?_⟩
  intro x hx
  rw [Finset.mem_coe] at hx
  rw [mem_box]; intro i
  calc (x i).natAbs ≤ Finset.univ.sup (fun j => (x j).natAbs) :=
        Finset.le_sup (f := fun j => (x j).natAbs) (Finset.mem_univ i)
    _ ≤ S.sup (fun y => Finset.univ.sup (fun j => (y j).natAbs)) :=
        Finset.le_sup (f := fun y => Finset.univ.sup (fun j => (y j).natAbs)) hx


theorem connWithinProb_le_one_su (p : NNReal) (hp : p ≤ 1) (S : Finset (Site d)) (x : Site d) :
    connWithinProb d p hp S x ≤ 1 := by
  classical
  unfold connWithinProb
  split
  · split
    · exact measureReal_le_one
    · norm_num
  · norm_num


theorem card_boundaryEdges_le_su (S : Finset (Site d)) :
    (boundaryEdges d S).card ≤ S.card * (2 * d) := by
  classical
  unfold boundaryEdges
  refine le_trans (Finset.card_image_le) ?_
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_product, Finset.card_product, Finset.card_univ, Finset.card_univ,
      Fintype.card_fin, Fintype.card_bool]
  ring_nf
  omega


theorem phi_le_card_su (p : NNReal) (hp : p ≤ 1) (S : Finset (Site d)) :
    phi d p hp S ≤ (p : ℝ) * (boundaryEdges d S).card := by
  unfold phi
  apply mul_le_mul_of_nonneg_left _ p.coe_nonneg
  calc ∑ e ∈ boundaryEdges d S, connWithinProb d p hp S e.1
      ≤ ∑ _e ∈ boundaryEdges d S, (1 : ℝ) :=
        Finset.sum_le_sum (fun e _ => connWithinProb_le_one_su p hp S e.1)
    _ = (boundaryEdges d S).card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]


theorem tildePc_pos (hd : 0 < d) : 0 < (tildePc d : ℝ) := by
  classical
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  set p : NNReal := 1 / (4 * d + 1) with hp_def
  have hpos : 0 < p := by rw [hp_def]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp_def, div_le_one (by positivity)]
    have h4d : (0 : NNReal) ≤ 4 * d := by positivity
    linarith
  set S : Finset (Site d) := {origin d} with hS_def
  have h0S : origin d ∈ S := by rw [hS_def]; exact Finset.mem_singleton_self _
  have hcard : (boundaryEdges d S).card ≤ 2 * d := by
    have := card_boundaryEdges_le_su S
    rwa [hS_def, Finset.card_singleton, one_mul] at this
  have hphi : phi d p hp1 S < 1 := by
    have hb := phi_le_card_su p hp1 S
    have hcardR : ((boundaryEdges d S).card : ℝ) ≤ 2 * d := by exact_mod_cast hcard
    have hpR : (p : ℝ) = 1 / (4 * d + 1) := by rw [hp_def]; push_cast; ring
    calc phi d p hp1 S ≤ (p : ℝ) * (boundaryEdges d S).card := hb
      _ ≤ (p : ℝ) * (2 * d) := mul_le_mul_of_nonneg_left hcardR p.coe_nonneg
      _ = (1 / (4 * d + 1)) * (2 * d) := by rw [hpR]
      _ < 1 := by rw [div_mul_eq_mul_div, div_lt_one (by positivity)]; linarith
  have hmem : p ∈ tildePcSet d := ⟨hp1, S, h0S, hphi⟩
  have hle : p ≤ tildePc d := le_csSup ⟨1, fun q hq => (mem_tildePcSet.mp hq).1⟩ hmem
  have : (0 : NNReal) < tildePc d := lt_of_lt_of_le hpos hle
  exact_mod_cast this


theorem wordEvent_adj_su (g : ℕ → Fin d × Bool) (n : ℕ) {ω : ConfigSpace (Sym2 (Site d))}
    (hω : ω ∈ wordEvent g n) (k : ℕ) (hk : k < n) :
    (openSubgraph d ω).Adj (vertOf g k) (vertOf g (k + 1)) := by
  rw [openSubgraph_adj]
  refine ⟨by rw [vertOf_succ]; exact adj_coordShift _ _ _, ?_⟩
  have := hω k (by simp [hk])
  unfold edgeOf at this
  rw [vertOf_succ] at this ⊢
  exact this


theorem wordEvent_connected_su (g : ℕ → Fin d × Bool) (n : ℕ)
    {ω : ConfigSpace (Sym2 (Site d))} (hω : ω ∈ wordEvent g n) :
    Connected d ω (origin d) (vertOf g n) := by
  induction n with
  | zero => simp only [vertOf]; exact connected_refl ω _
  | succ k ih =>
    have hωk : ω ∈ wordEvent g k :=
      fun j hj => hω j (by simp only [Finset.mem_range] at hj ⊢; omega)
    exact (ih hωk).trans (SimpleGraph.Adj.reachable (wordEvent_adj_su g (k + 1) hω k (by omega)))


end Percolation
end StatMech
