/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wndwinding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Def.StatisticalMechanics.Code.Walls.wndwinding.Part2
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

@[simp] theorem wnd_signedCross_nil (z x : Site 2) :
    wnd_signedCross z (SimpleGraph.Walk.nil : (hypercubicLattice 2).Walk x x) = 0 := by
  classical simp [wnd_signedCross]


theorem wnd_signedCross_append (z : Site 2) {x y w' : Site 2}
    (p : (hypercubicLattice 2).Walk x y) (q : (hypercubicLattice 2).Walk y w') :
    wnd_signedCross z (p.append q) = wnd_signedCross z p + wnd_signedCross z q := by
  classical
  unfold wnd_signedCross
  rw [SimpleGraph.Walk.darts_append, List.map_append, List.sum_append]


theorem wnd_signedCross_reverse (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    wnd_signedCross z w.reverse = - wnd_signedCross z w := by
  classical
  unfold wnd_signedCross
  rw [SimpleGraph.Walk.darts_reverse, List.map_reverse, List.sum_reverse, List.map_map]
  have hmap : (w.darts.map ((fun d => wnd_signStep z d.toProd.1 d.toProd.2) ∘ Dart.symm))
      = w.darts.map (fun d => - wnd_signStep z d.toProd.1 d.toProd.2) := by
    apply List.map_congr_left
    intro d _
    show wnd_signStep z d.symm.toProd.1 d.symm.toProd.2 = _
    rw [show d.symm.toProd.1 = d.toProd.2 from rfl, show d.symm.toProd.2 = d.toProd.1 from rfl]
    exact wnd_signStep_swap z d.toProd.1 d.toProd.2
  rw [hmap]
  rw [show (fun d : (hypercubicLattice 2).Dart => - wnd_signStep z d.toProd.1 d.toProd.2)
      = (fun x : ℤ => -x) ∘ (fun d => wnd_signStep z d.toProd.1 d.toProd.2) from rfl,
    ← List.map_map, List.sum_neg]


open Classical in


theorem wnd_rayCount_eq_darts_sum (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    (jec_rayCount z w : ℤ) =
      (w.darts.map (fun d => if jec_rayEdge z d.edge then (1 : ℤ) else 0)).sum := by
  classical
  rw [jec_rayCount, SimpleGraph.Walk.edges, List.countP_map]
  induction w.darts with
  | nil => simp
  | cons d t ih =>
    rw [List.countP_cons, List.map_cons, List.sum_cons, ← ih]
    by_cases h : jec_rayEdge z d.edge
    · simp only [Function.comp_apply, h, if_pos, decide_true]
      push_cast; ring
    · rw [if_neg h]
      have : ¬ (jec_rayEdge z ((Dart.edge) d)) := h
      simp only [Function.comp_apply, decide_eq_true_eq, this, if_false, Nat.add_zero,
        zero_add]


theorem wnd_signedCross_abs_le_rayCount (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    |wnd_signedCross z w| ≤ (jec_rayCount z w : ℤ) := by
  classical
  unfold wnd_signedCross
  rw [wnd_rayCount_eq_darts_sum z w]
  
  have habs : |(w.darts.map (fun d => wnd_signStep z d.toProd.1 d.toProd.2)).sum|
      ≤ (w.darts.map (fun d => |wnd_signStep z d.toProd.1 d.toProd.2|)).sum := by
    induction w.darts with
    | nil => simp
    | cons d t ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      calc |wnd_signStep z d.toProd.1 d.toProd.2
              + (t.map (fun d => wnd_signStep z d.toProd.1 d.toProd.2)).sum|
          ≤ |wnd_signStep z d.toProd.1 d.toProd.2|
              + |(t.map (fun d => wnd_signStep z d.toProd.1 d.toProd.2)).sum| :=
            abs_add_le _ _
        _ ≤ |wnd_signStep z d.toProd.1 d.toProd.2|
              + (t.map (fun d => |wnd_signStep z d.toProd.1 d.toProd.2|)).sum := by linarith
  refine le_trans habs (le_of_eq ?_)
  congr 1
  apply List.map_congr_left
  intro d _
  rw [wnd_abs_signStep_eq_indicator z d.toProd.1 d.toProd.2]
  rw [show d.edge = s(d.toProd.1, d.toProd.2) from rfl]


theorem wnd_signedCross_parity (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) :
    wnd_signedCross z w % 2 = (jec_rayCount z w : ℤ) % 2 := by
  classical
  unfold wnd_signedCross
  rw [wnd_rayCount_eq_darts_sum z w]
  
  induction w.darts with
  | nil => simp
  | cons d t ih =>
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      Int.add_emod, Int.add_emod (if jec_rayEdge z d.edge then (1 : ℤ) else 0), ih]
    have hstep : wnd_signStep z d.toProd.1 d.toProd.2 % 2
        = (if jec_rayEdge z d.edge then (1 : ℤ) else 0) % 2 := by
      rw [wnd_signStep_parity z d.toProd.1 d.toProd.2,
        show d.edge = s(d.toProd.1, d.toProd.2) from rfl]
    rw [hstep]


theorem wnd_signedCross_ne_zero_of_rayCount_odd (z : Site 2) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y) (hodd : ¬ Even (jec_rayCount z w)) :
    wnd_signedCross z w ≠ 0 := by
  classical
  have hpar := wnd_signedCross_parity z w
  rw [Nat.not_even_iff] at hodd
  have hrayodd : (jec_rayCount z w : ℤ) % 2 = 1 := by
    have hc : ((jec_rayCount z w : ℤ) % 2) = ((jec_rayCount z w % 2 : ℕ) : ℤ) := by
      push_cast; ring
    rw [hc, hodd]; rfl
  intro hz
  rw [hz] at hpar
  simp only [Int.zero_emod] at hpar
  rw [hrayodd] at hpar
  exact absurd hpar.symm (by decide)


end Lattice
end StatMech
