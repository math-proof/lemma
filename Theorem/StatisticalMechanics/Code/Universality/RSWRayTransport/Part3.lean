/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWRayTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.RSWOuterStraddle.Part2
import Def.StatisticalMechanics.Code.Universality.RSWRayTransport.Part2
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_rayEdge_dualReflect_iff {z u v : Site 2}
    (hadj : (hypercubicLattice 2).Adj u v) :
    jec_rayEdge (rlc_primalDualReflect z)
        s(rlc_dualReflect u, rlc_dualReflect v) ↔
      bdEdge (jec_belowSet (z 1)) s(u, v) ∧
        ¬ jec_rayEdge z s(u, v) := by
  rw [jec_rayEdge_mk, jec_belowSet_bdEdge (z 1) u v hadj,
    jec_rayEdge_mk]
  simp only [rlc_primalDualReflect_zero, rlc_primalDualReflect_one,
    rlc_dualReflect_zero, rlc_dualReflect_one]
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  omega

theorem rlc_countP_complement_within
    {E : Type*} (l : List E) (P Q : E → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hsub : ∀ e ∈ l, P e → Q e) :
    l.countP (fun e => decide (Q e ∧ ¬ P e)) +
        l.countP (fun e => decide (P e)) =
      l.countP (fun e => decide (Q e)) := by
  induction l with
  | nil => simp
  | cons e l ih =>
      have hesub : P e → Q e := hsub e (by simp)
      have hlsub : ∀ f ∈ l, P f → Q f := by
        intro f hf
        exact hsub f (by simp [hf])
      specialize ih hlsub
      simp only [List.countP_cons]
      by_cases hP : P e <;> by_cases hQ : Q e <;> simp_all <;> omega


theorem rlc_rayParity_dualReflect_map {a : Site 2}
    (w : (hypercubicLattice 2).Walk a a) (z : Site 2) :
    Even (jec_rayCount (rlc_primalDualReflect z)
      (w.map rlc_dualReflectLatticeHom)) ↔
      Even (jec_rayCount z w) := by
  classical
  have hcount :
      jec_rayCount (rlc_primalDualReflect z)
          (w.map rlc_dualReflectLatticeHom) + jec_rayCount z w =
        crossCount (jec_belowSet (z 1)) w := by
    rw [jec_rayCount, SimpleGraph.Walk.edges_map, List.countP_map,
      jec_rayCount, crossCount]
    change
      w.edges.countP (fun e => decide
          (jec_rayEdge (rlc_primalDualReflect z)
            (Sym2.map rlc_dualReflectLatticeHom e))) +
        w.edges.countP (fun e => decide (jec_rayEdge z e)) =
      w.edges.countP (fun e => decide
        (bdEdge (jec_belowSet (z 1)) e))
    have hreflect :
        w.edges.countP (fun e => decide
          (jec_rayEdge (rlc_primalDualReflect z)
            (Sym2.map rlc_dualReflectLatticeHom e))) =
        w.edges.countP (fun e => decide
          (bdEdge (jec_belowSet (z 1)) e ∧ ¬ jec_rayEdge z e)) := by
      apply List.countP_congr
      intro e he
      induction e using Sym2.inductionOn with
      | _ u v =>
          simp only [Sym2.map_mk, decide_eq_true_eq]
          exact rlc_rayEdge_dualReflect_iff (w.adj_of_mem_edges he)
    rw [hreflect]
    exact rlc_countP_complement_within w.edges
      (jec_rayEdge z) (bdEdge (jec_belowSet (z 1))) (by
        intro e he hray
        induction e using Sym2.inductionOn with
        | _ u v =>
            have hadj := w.adj_of_mem_edges he
            rw [jec_rayEdge_mk] at hray
            rw [jec_belowSet_bdEdge (z 1) u v hadj]
            exact ⟨hray.1.1, hray.2⟩)
  have htotal : Even (crossCount (jec_belowSet (z 1)) w) :=
    crossCount_even_of_loop (jec_belowSet (z 1)) w
  rw [← hcount] at htotal
  exact Nat.even_add.mp htotal


end Universality
end StatMech
