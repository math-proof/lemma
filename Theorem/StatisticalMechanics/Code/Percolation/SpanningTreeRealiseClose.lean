/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeRealiseClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Instance.StatisticalMechanics.Code.Percolation.SpanningTreeRealiseClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


variable {N : Type*} [Fintype N] [DecidableEq N]

omit [Fintype N] in

theorem str_spider_adj (a b : str_SpiderV N) :
    (str_spiderG N).Adj a b ↔ a ≠ b ∧ (str_sAdj a b = true ∨ str_sAdj b a = true) := by
  rw [str_spiderG, fromRel_adj]

omit [Fintype N] in

theorem str_spider_reach_root (v : str_SpiderV N) : (str_spiderG N).Reachable none v := by
  match v with
  | none => exact Reachable.refl _
  | some (Sum.inl i) =>
      exact Adj.reachable (by rw [str_spider_adj]; exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩)
  | some (Sum.inr p) =>
      have h1 : (str_spiderG N).Adj none (some (Sum.inl p.1)) := by
        rw [str_spider_adj]; exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩
      have h2 : (str_spiderG N).Adj (some (Sum.inl p.1)) (some (Sum.inr p)) := by
        rw [str_spider_adj]; exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩
      exact (h1.reachable).trans (h2.reachable)

omit [Fintype N] in

theorem str_spiderG_connected : (str_spiderG N).Connected := by
  rw [connected_iff_exists_forall_reachable]; exact ⟨none, fun w => str_spider_reach_root w⟩


theorem str_spider_leaf_deg (p : N × Fin 2) : (str_spiderG N).degree (some (Sum.inr p)) = 1 := by
  rw [← card_neighborFinset_eq_degree]
  have hset : (str_spiderG N).neighborFinset (some (Sum.inr p)) = {some (Sum.inl p.1)} := by
    ext v
    rw [mem_neighborFinset, str_spider_adj]
    constructor
    · rintro ⟨hne, hor⟩
      match v with
      | none => simp [str_sAdj] at hor
      | some (Sum.inl i) =>
          rw [Finset.mem_singleton]
          have hip : i = p.1 := by
            rcases hor with h | h <;> · simp only [str_sAdj] at h; simpa using h
          rw [hip]
      | some (Sum.inr q) => simp [str_sAdj] at hor
    · intro hv; rw [Finset.mem_singleton] at hv; subst hv
      exact ⟨by simp, Or.inr (by simp [str_sAdj])⟩
  rw [hset, Finset.card_singleton]


theorem str_spider_hub_deg (i : N) : (str_spiderG N).degree (some (Sum.inl i)) = 3 := by
  rw [← card_neighborFinset_eq_degree]
  have hset : (str_spiderG N).neighborFinset (some (Sum.inl i))
      = {none, some (Sum.inr (i, 0)), some (Sum.inr (i, 1))} := by
    ext v
    rw [mem_neighborFinset, str_spider_adj]
    constructor
    · rintro ⟨hne, hor⟩
      match v with
      | none => simp
      | some (Sum.inl j) => rcases hor with h | h <;> simp [str_sAdj] at h
      | some (Sum.inr q) =>
          have hiq : i = q.1 := by
            rcases hor with h | h <;> · simp only [str_sAdj] at h; exact (by simpa using h)
          have hv : (Sum.inr q : N ⊕ N × Fin 2) = Sum.inr (i, q.2) := by simp [hiq]
          rw [hv]
          have : q.2 = 0 ∨ q.2 = 1 := by omega
          rcases this with h2 | h2 <;> simp [h2]
    · intro hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩
      · exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩
      · exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩
  rw [hset, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_singleton]


theorem str_spider_root_deg : (str_spiderG N).degree none = Fintype.card N := by
  rw [← card_neighborFinset_eq_degree]
  have hset : (str_spiderG N).neighborFinset (none : str_SpiderV N)
      = (univ : Finset N).image (fun i => some (Sum.inl i)) := by
    ext v
    rw [mem_neighborFinset, str_spider_adj, Finset.mem_image]
    constructor
    · rintro ⟨hne, hor⟩
      match v with
      | none => simp at hne
      | some (Sum.inl j) => exact ⟨j, Finset.mem_univ _, rfl⟩
      | some (Sum.inr q) => rcases hor with h | h <;> simp [str_sAdj] at h
    · rintro ⟨i, _, rfl⟩
      exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩
  rw [hset, Finset.card_image_of_injective _ (by intro a b h; simpa using h), Finset.card_univ]


theorem str_spider_sum_deg : ∑ v, (str_spiderG N).degree v = 6 * Fintype.card N := by
  rw [Fintype.sum_option, Fintype.sum_sum_type, str_spider_root_deg]
  simp only [str_spider_hub_deg, str_spider_leaf_deg]
  rw [Finset.sum_const, Finset.sum_const]
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul, mul_one]
  ring

omit [DecidableEq N] in

theorem str_spider_card_V : Fintype.card (str_SpiderV N) = 1 + 3 * Fintype.card N := by
  simp only [str_SpiderV, Fintype.card_option, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin]
  ring


theorem str_spider_edge_card : (str_spiderG N).edgeFinset.card = 3 * Fintype.card N := by
  have h := (str_spiderG N).sum_degrees_eq_twice_card_edges
  rw [str_spider_sum_deg] at h; omega


theorem str_spiderG_isTree : (str_spiderG N).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨str_spiderG_connected, ?_⟩
  have hcard : Nat.card (str_spiderG N).edgeSet = (str_spiderG N).edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]; rfl
  rw [hcard, str_spider_edge_card, Nat.card_eq_fintype_card, str_spider_card_V]; ring

omit [DecidableEq N] in

theorem str_spider_two_le_card (hN : 1 ≤ Fintype.card N) : 2 ≤ Fintype.card (str_SpiderV N) := by
  rw [str_spider_card_V]; omega


theorem str_spider_leaf_cases (v : str_SpiderV N) (hv : (str_spiderG N).degree v = 1) :
    v = none ∨ ∃ p, v = some (Sum.inr p) := by
  match v with
  | none => left; rfl
  | some (Sum.inl i) => rw [str_spider_hub_deg] at hv; omega
  | some (Sum.inr p) => right; exact ⟨p, rfl⟩


end Percolation
end StatMech
