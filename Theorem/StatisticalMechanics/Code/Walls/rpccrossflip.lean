/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rpccrossflip.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitWindingWitness.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.kwceventtocut.Part3
import Def.StatisticalMechanics.Code.Walls.rpccrossflip
open Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice


@[simp] theorem rpc_hCrossEdge_isRayEdge_left (u : Site 2) :
    ¬ jec_rayEdge u (rpc_hCrossEdge u) := by
  rw [rpc_hCrossEdge, jec_rayEdge_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  omega


theorem rpc_hCrossEdge_isRayEdge_right (u v : Site 2) (h0 : v 0 = u 0 + 1)
    (h1 : v 1 = u 1) : jec_rayEdge v (rpc_hCrossEdge u) := by
  rw [rpc_hCrossEdge, jec_rayEdge_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  refine ⟨⟨trivial, by omega⟩, Or.inl ⟨by omega, by omega⟩⟩


theorem rpc_rayEdge_horizontalStep (u v : Site 2) (h0 : v 0 = u 0 + 1) (h1 : v 1 = u 1)
    {p q : Site 2} (_hadj : (hypercubicLattice 2).Adj p q) :
    jec_rayEdge v s(p, q) ↔ (jec_rayEdge u s(p, q) ∨ s(p, q) = rpc_hCrossEdge u) := by
  rw [jec_rayEdge_mk, jec_rayEdge_mk, rpc_hCrossEdge, Sym2.eq_iff]
  constructor
  · rintro ⟨⟨hpq0, hp0⟩, hstr⟩
    rcases hstr with ⟨hp1, hq1⟩ | ⟨hq1, hp1⟩
    · 
      by_cases hlt : p 0 ≤ u 0 - 1
      · exact Or.inl ⟨⟨hpq0, hlt⟩, Or.inl ⟨by omega, by omega⟩⟩
      · 
        have hp0e : p 0 = u 0 := by omega
        have hq0e : q 0 = u 0 := by omega
        have hp1e : p 1 = u 1 - 1 := by omega
        have hq1e : q 1 = u 1 := by omega
        right; left
        constructor <;> (funext i; fin_cases i) <;> simp_all
    · by_cases hlt : p 0 ≤ u 0 - 1
      · exact Or.inl ⟨⟨hpq0, hlt⟩, Or.inr ⟨by omega, by omega⟩⟩
      · have hp0e : p 0 = u 0 := by omega
        have hq0e : q 0 = u 0 := by omega
        have hp1e : p 1 = u 1 := by omega
        have hq1e : q 1 = u 1 - 1 := by omega
        right; right
        constructor <;> (funext i; fin_cases i) <;> simp_all
  · rintro (⟨⟨hpq0, hp0⟩, hstr⟩ | hcross)
    · refine ⟨⟨hpq0, by omega⟩, ?_⟩
      rcases hstr with ⟨hp1, hq1⟩ | ⟨hq1, hp1⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · 
      rcases hcross with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, hq]; simp only [Matrix.cons_val_zero]
        · rw [hp]; simp only [Matrix.cons_val_zero]; omega
        · left; constructor
          · rw [hp]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
          · rw [hq]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, hq]; simp only [Matrix.cons_val_zero]
        · rw [hp]; simp only [Matrix.cons_val_zero]; omega
        · right; constructor
          · rw [hq]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
          · rw [hp]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega


open Classical in


theorem rpc_rayCount_edges_split (u v : Site 2) (h0 : v 0 = u 0 + 1) (h1 : v 1 = u 1)
    (l : List (Sym2 (Site 2))) (hl : ∀ e ∈ l, ∃ p q, e = s(p, q) ∧ (hypercubicLattice 2).Adj p q) :
    l.countP (fun e => decide (jec_rayEdge v e)) =
      l.countP (fun e => decide (jec_rayEdge u e)) + l.count (rpc_hCrossEdge u) := by
  classical
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun e he => hl e (List.mem_cons_of_mem a he))
    obtain ⟨p, q, rfl, hadj⟩ := hl a (List.mem_cons_self ..)
    rw [List.countP_cons, List.countP_cons, List.count_cons]
    have hdich := rpc_rayEdge_horizontalStep u v h0 h1 hadj
    have hexcl : ¬ (jec_rayEdge u s(p, q) ∧ s(p, q) = rpc_hCrossEdge u) := by
      rintro ⟨hru, heq⟩
      exact rpc_hCrossEdge_isRayEdge_left u (heq ▸ hru)
    by_cases hru : jec_rayEdge u s(p, q)
    · have hrv : jec_rayEdge v s(p, q) := hdich.mpr (Or.inl hru)
      have hne : s(p, q) ≠ rpc_hCrossEdge u := fun h => hexcl ⟨hru, h⟩
      rw [if_pos (by simp [hrv]), if_pos (by simp [hru])]
      rw [ih']; simp only [beq_iff_eq, hne, ite_false]; omega
    · by_cases hcross : s(p, q) = rpc_hCrossEdge u
      · have hrv : jec_rayEdge v s(p, q) := hdich.mpr (Or.inr hcross)
        rw [if_pos (by simp [hrv]), if_neg (by simp [hru])]
        rw [ih']; simp only [beq_iff_eq, hcross, if_pos]; omega
      · have hrv : ¬ jec_rayEdge v s(p, q) := by
          intro h; rcases hdich.mp h with h' | h'
          · exact hru h'
          · exact hcross h'
        rw [if_neg (by simp [hrv]), if_neg (by simp [hru])]
        rw [ih']; simp only [beq_iff_eq, hcross, ite_false]; omega


theorem rpc_rayCount_horizontalStep_diff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (u v : Site 2) (h0 : v 0 = u 0 + 1) (h1 : v 1 = u 1) :
    jec_rayCount v Vc = jec_rayCount u Vc + Vc.edges.count (rpc_hCrossEdge u) := by
  classical
  rw [jec_rayCount, jec_rayCount]
  exact rpc_rayCount_edges_split u v h0 h1 Vc.edges (fun e he => by
    obtain ⟨p, q⟩ := e
    exact ⟨p, q, rfl, Vc.adj_of_mem_edges he⟩)


theorem rpc_horizontalFlip_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (u v : Site 2) (h0 : v 0 = u 0 + 1) (h1 : v 1 = u 1) :
    (Even (jec_rayCount u Vc) ↔ ¬ Even (jec_rayCount v Vc)) ↔
      Odd (Vc.edges.count (rpc_hCrossEdge u)) := by
  rw [rpc_rayCount_horizontalStep_diff Vc u v h0 h1, Nat.even_add,
    ← Nat.not_even_iff_odd]
  by_cases hu : Even (jec_rayCount u Vc) <;>
    by_cases hc : Even (Vc.edges.count (rpc_hCrossEdge u)) <;>
    simp only [hu, hc, iff_true, iff_false, not_true, not_false_iff]


end Walls
end StatMech
