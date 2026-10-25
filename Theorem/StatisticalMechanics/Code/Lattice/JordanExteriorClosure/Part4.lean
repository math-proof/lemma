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
import Def.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part4
open Set SimpleGraph


namespace StatMech

namespace Lattice

open StatMech.RSW.Box


@[simp] theorem jec_rayCount_nil (z x : Site 2) :
    jec_rayCount z (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
  classical simp [jec_rayCount]

@[simp] theorem jec_wallCount_nil (z x : Site 2) :
    jec_wallCount z (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
  classical simp [jec_wallCount]


theorem jec_rayCount_append (z : Site 2) {x y w' : Site 2}
    (p : (hypercubicLattice 2).Walk x y) (q : (hypercubicLattice 2).Walk y w') :
    jec_rayCount z (p.append q) = jec_rayCount z p + jec_rayCount z q := by
  classical
  rw [jec_rayCount, jec_rayCount, jec_rayCount, SimpleGraph.Walk.edges_append,
    List.countP_append]


theorem jec_rayCount_copy (z : Site 2) {x y x' y' : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hu : x = x') (hv : y = y') :
    jec_rayCount z (w.copy hu hv) = jec_rayCount z w := by
  classical rw [jec_rayCount, jec_rayCount, SimpleGraph.Walk.edges_copy]


theorem jec_rayCount_reverse (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    jec_rayCount z w.reverse = jec_rayCount z w := by
  classical
  rw [jec_rayCount, jec_rayCount, SimpleGraph.Walk.edges_reverse, List.countP_reverse]

theorem jec_countP_disjoint_split (l : List (Sym2 (Site 2)))
    (Q R : Sym2 (Site 2) → Prop) [DecidablePred Q] [DecidablePred R]
    (hdec : ∀ e ∈ l, ¬ (Q e ∧ R e)) :
    l.countP (fun e => decide (Q e ∨ R e)) =
      l.countP (fun e => decide (Q e)) + l.countP (fun e => decide (R e)) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    rw [List.countP_cons, List.countP_cons, List.countP_cons]
    have hexcl : ¬ (Q a ∧ R a) := hdec a (List.mem_cons_self ..)
    have ih' := ih (fun e he => hdec e (List.mem_cons_of_mem a he))
    by_cases hQ : Q a <;> by_cases hR : R a <;> simp_all <;> omega


theorem jec_crossCount_quad_decomp (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    crossCount (jec_quad z) w = jec_rayCount z w + jec_wallCount z w := by
  classical
  rw [crossCount, jec_rayCount, jec_wallCount]
  have key : ∀ e ∈ w.edges,
      (decide (bdEdge (jec_quad z) e) = true ↔
        decide (jec_rayEdge z e ∨ jec_wallEdge z e) = true) := by
    intro e he
    obtain ⟨u, v⟩ := e
    have hadj : (hypercubicLattice 2).Adj u v := w.adj_of_mem_edges he
    simp only [decide_eq_true_eq]
    exact jec_quad_bdEdge_iff z u v hadj
  rw [List.countP_congr key]
  refine jec_countP_disjoint_split w.edges (jec_rayEdge z) (jec_wallEdge z) ?_
  intro e _he
  obtain ⟨u, v⟩ := e
  exact jec_ray_wall_excl z u v


theorem jec_rayCount_horizontalStep (z z' : Site 2) (hz'0 : z' 0 = z 0 + 1)
    (hz'1 : z' 1 = z 1) {x y : Site 2} (w : (hypercubicLattice 2).Walk x y)
    (hz : z ∉ w.support) :
    jec_rayCount z' w = jec_rayCount z w := by
  classical
  rw [jec_rayCount, jec_rayCount]
  refine List.countP_congr ?_
  intro e he
  obtain ⟨p, q⟩ := e
  have hadj : (hypercubicLattice 2).Adj p q := w.adj_of_mem_edges he
  have hp : p ∈ w.support := w.fst_mem_support_of_mem_edges he
  have hq : q ∈ w.support := w.snd_mem_support_of_mem_edges he
  simp only [decide_eq_true_eq, jec_rayEdge_mk]
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, ?_⟩
    · by_contra hcon
      push Not at hcon
      have hp0 : p 0 = z 0 := by omega
      rcases h3 with ⟨hpr, hqr⟩ | ⟨hqr, hpr⟩
      · rw [hz'1] at hqr
        have hq0 : q 0 = z 0 := by omega
        have hq1 : q 1 = z 1 := hqr
        have : q = z := by funext i; fin_cases i <;> assumption
        exact hz (this ▸ hq)
      · rw [hz'1] at hpr
        have hp1 : p 1 = z 1 := hpr
        have : p = z := by funext i; fin_cases i <;> assumption
        exact hz (this ▸ hp)
    · rw [hz'1] at h3; exact h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, by omega⟩, by rw [hz'1]; exact h3⟩


theorem jec_wallCount_verticalStep (z z' : Site 2) (hz'0 : z' 0 = z 0)
    (hz'1 : z' 1 = z 1 + 1) {x y : Site 2} (w : (hypercubicLattice 2).Walk x y)
    (hz : z ∉ w.support) :
    jec_wallCount z' w = jec_wallCount z w := by
  classical
  rw [jec_wallCount, jec_wallCount]
  refine List.countP_congr ?_
  intro e he
  obtain ⟨p, q⟩ := e
  have hadj : (hypercubicLattice 2).Adj p q := w.adj_of_mem_edges he
  have hp : p ∈ w.support := w.fst_mem_support_of_mem_edges he
  have hq : q ∈ w.support := w.snd_mem_support_of_mem_edges he
  simp only [decide_eq_true_eq, jec_wallEdge_mk]
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨⟨h1, ?_⟩, ?_⟩
    · by_contra hcon
      push Not at hcon
      have hp1 : p 1 = z 1 := by omega
      rcases h3 with ⟨hpc, hqc⟩ | ⟨hqc, hpc⟩
      · rw [hz'0] at hqc
        have hq1 : q 1 = z 1 := by omega
        have hq0 : q 0 = z 0 := hqc
        have : q = z := by funext i; fin_cases i <;> assumption
        exact hz (this ▸ hq)
      · rw [hz'0] at hpc
        have hp0 : p 0 = z 0 := hpc
        have : p = z := by funext i; fin_cases i <;> assumption
        exact hz (this ▸ hp)
    · rw [hz'0] at h3; exact h3
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨h1, by omega⟩, by rw [hz'0]; exact h3⟩


theorem jec_loop_ray_wall_parity (z : Site 2) {a : Site 2}
    (Vc : (hypercubicLattice 2).Walk a a) :
    Even (jec_rayCount z Vc) ↔ Even (jec_wallCount z Vc) := by
  have heven : Even (crossCount (jec_quad z) Vc) := crossCount_even_of_loop (jec_quad z) Vc
  rw [jec_crossCount_quad_decomp z Vc, Nat.even_add] at heven
  exact heven


theorem jec_localConstancy {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hu : u ∉ Vc.support) (hv : v ∉ Vc.support) :
    (Even (jec_rayCount u Vc) ↔ Even (jec_rayCount v Vc)) := by
  have hadj' := hadj
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj'
  
  by_cases hc0 : u 0 = v 0
  · 
    have hc1 : u 1 = v 1 + 1 ∨ v 1 = u 1 + 1 := by omega
    rcases hc1 with h | h
    · 
      have hwall : jec_wallCount u Vc = jec_wallCount v Vc :=
        jec_wallCount_verticalStep v u (by omega) (by omega) Vc hv
      rw [jec_loop_ray_wall_parity u Vc, jec_loop_ray_wall_parity v Vc, hwall]
    · 
      have hwall : jec_wallCount v Vc = jec_wallCount u Vc :=
        jec_wallCount_verticalStep u v (by omega) (by omega) Vc hu
      rw [jec_loop_ray_wall_parity u Vc, jec_loop_ray_wall_parity v Vc, hwall]
  · 
    have hc0' : u 0 = v 0 + 1 ∨ v 0 = u 0 + 1 := by omega
    rcases hc0' with h | h
    · have hray : jec_rayCount u Vc = jec_rayCount v Vc :=
        jec_rayCount_horizontalStep v u (by omega) (by omega) Vc hv
      rw [hray]
    · have hray : jec_rayCount v Vc = jec_rayCount u Vc :=
        jec_rayCount_horizontalStep u v (by omega) (by omega) Vc hu
      rw [hray]


end Lattice
end StatMech
