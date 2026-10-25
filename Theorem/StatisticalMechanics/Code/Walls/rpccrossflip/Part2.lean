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
import Def.StatisticalMechanics.Code.Walls.rpccrossflip.Part2
open Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem rpc_vCrossEdge_isWallEdge_left (u : Site 2) : ¬ jec_wallEdge u (rpc_vCrossEdge u) := by
  rw [rpc_vCrossEdge, jec_wallEdge_mk]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  omega


theorem rpc_wallEdge_verticalStep (u v : Site 2) (h0 : v 0 = u 0) (h1 : v 1 = u 1 + 1)
    {p q : Site 2} (_hadj : (hypercubicLattice 2).Adj p q) :
    jec_wallEdge v s(p, q) ↔ (jec_wallEdge u s(p, q) ∨ s(p, q) = rpc_vCrossEdge u) := by
  rw [jec_wallEdge_mk, jec_wallEdge_mk, rpc_vCrossEdge, Sym2.eq_iff]
  constructor
  · rintro ⟨⟨hpq1, hp1⟩, hstr⟩
    rcases hstr with ⟨hp0, hq0⟩ | ⟨hq0, hp0⟩
    · by_cases hle : p 1 ≤ u 1 - 1
      · exact Or.inl ⟨⟨hpq1, hle⟩, Or.inl ⟨by omega, by omega⟩⟩
      · have hp1e : p 1 = u 1 := by omega
        have hq1e : q 1 = u 1 := by omega
        have hp0e : p 0 = u 0 - 1 := by omega
        have hq0e : q 0 = u 0 := by omega
        right; left
        constructor <;> (funext i; fin_cases i) <;> simp_all
    · by_cases hle : p 1 ≤ u 1 - 1
      · exact Or.inl ⟨⟨hpq1, hle⟩, Or.inr ⟨by omega, by omega⟩⟩
      · have hp1e : p 1 = u 1 := by omega
        have hq1e : q 1 = u 1 := by omega
        have hp0e : p 0 = u 0 := by omega
        have hq0e : q 0 = u 0 - 1 := by omega
        right; right
        constructor <;> (funext i; fin_cases i) <;> simp_all
  · rintro (⟨⟨hpq1, hp1⟩, hstr⟩ | hcross)
    · refine ⟨⟨hpq1, by omega⟩, ?_⟩
      rcases hstr with ⟨hp0, hq0⟩ | ⟨hq0, hp0⟩
      · exact Or.inl ⟨by omega, by omega⟩
      · exact Or.inr ⟨by omega, by omega⟩
    · rcases hcross with ⟨hp, hq⟩ | ⟨hp, hq⟩
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, hq]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
        · rw [hp]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
        · left; constructor
          · rw [hp]; simp only [Matrix.cons_val_zero]; omega
          · rw [hq]; simp only [Matrix.cons_val_zero]; omega
      · refine ⟨⟨?_, ?_⟩, ?_⟩
        · rw [hp, hq]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]
        · rw [hp]; simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one]; omega
        · right; constructor
          · rw [hq]; simp only [Matrix.cons_val_zero]; omega
          · rw [hp]; simp only [Matrix.cons_val_zero]; omega

open Classical in

theorem rpc_wallCount_edges_split (u v : Site 2) (h0 : v 0 = u 0) (h1 : v 1 = u 1 + 1)
    (l : List (Sym2 (Site 2))) (hl : ∀ e ∈ l, ∃ p q, e = s(p, q) ∧ (hypercubicLattice 2).Adj p q) :
    l.countP (fun e => decide (jec_wallEdge v e)) =
      l.countP (fun e => decide (jec_wallEdge u e)) + l.count (rpc_vCrossEdge u) := by
  classical
  induction l with
  | nil => simp
  | cons a t ih =>
    have ih' := ih (fun e he => hl e (List.mem_cons_of_mem a he))
    obtain ⟨p, q, rfl, hadj⟩ := hl a (List.mem_cons_self ..)
    rw [List.countP_cons, List.countP_cons, List.count_cons]
    have hdich := rpc_wallEdge_verticalStep u v h0 h1 hadj
    have hexcl : ¬ (jec_wallEdge u s(p, q) ∧ s(p, q) = rpc_vCrossEdge u) := by
      rintro ⟨hwu, heq⟩
      exact rpc_vCrossEdge_isWallEdge_left u (heq ▸ hwu)
    by_cases hwu : jec_wallEdge u s(p, q)
    · have hwv : jec_wallEdge v s(p, q) := hdich.mpr (Or.inl hwu)
      have hne : s(p, q) ≠ rpc_vCrossEdge u := fun h => hexcl ⟨hwu, h⟩
      rw [if_pos (by simp [hwv]), if_pos (by simp [hwu])]
      rw [ih']; simp only [beq_iff_eq, hne, ite_false]; omega
    · by_cases hcross : s(p, q) = rpc_vCrossEdge u
      · have hwv : jec_wallEdge v s(p, q) := hdich.mpr (Or.inr hcross)
        rw [if_pos (by simp [hwv]), if_neg (by simp [hwu])]
        rw [ih']; simp only [beq_iff_eq, hcross, ite_true]; omega
      · have hwv : ¬ jec_wallEdge v s(p, q) := by
          intro h; rcases hdich.mp h with h' | h'
          · exact hwu h'
          · exact hcross h'
        rw [if_neg (by simp [hwv]), if_neg (by simp [hwu])]
        rw [ih']; simp only [beq_iff_eq, hcross, ite_false]; omega


theorem rpc_wallCount_verticalStep_diff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (u v : Site 2) (h0 : v 0 = u 0) (h1 : v 1 = u 1 + 1) :
    jec_wallCount v Vc = jec_wallCount u Vc + Vc.edges.count (rpc_vCrossEdge u) := by
  classical
  rw [jec_wallCount, jec_wallCount]
  exact rpc_wallCount_edges_split u v h0 h1 Vc.edges (fun e he => by
    obtain ⟨p, q⟩ := e
    exact ⟨p, q, rfl, Vc.adj_of_mem_edges he⟩)


theorem rpc_verticalFlip_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (u v : Site 2) (h0 : v 0 = u 0) (h1 : v 1 = u 1 + 1) :
    (Even (jec_rayCount u Vc) ↔ ¬ Even (jec_rayCount v Vc)) ↔
      Odd (Vc.edges.count (rpc_vCrossEdge u)) := by
  rw [jec_loop_ray_wall_parity u Vc, jec_loop_ray_wall_parity v Vc,
    rpc_wallCount_verticalStep_diff Vc u v h0 h1, Nat.even_add, ← Nat.not_even_iff_odd]
  by_cases hu : Even (jec_wallCount u Vc) <;>
    by_cases hc : Even (Vc.edges.count (rpc_vCrossEdge u)) <;>
    simp only [hu, hc, iff_true, iff_false, not_true, not_false_iff]


end Walls
end StatMech
