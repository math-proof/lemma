/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wpdprimaldegree.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Theorem.StatisticalMechanics.Code.Walls.wnaalternate.Part3
import Theorem.StatisticalMechanics.Code.Walls.wcbcolumnbridge.Part4
import Theorem.StatisticalMechanics.Code.Walls.wstsigntoggle.Part2
import Theorem.StatisticalMechanics.Code.Walls.rpccrossflip.Part4
import Theorem.StatisticalMechanics.Code.Walls.wisindicatorsteps.Part5
import Theorem.StatisticalMechanics.Code.Walls.wosorientedsign.Part2
import Theorem.StatisticalMechanics.Code.Walls.welenterleave.Part2
import Theorem.StatisticalMechanics.Code.Walls.woborientbridge.Part4
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wpd_signStep_up_iff (z u v : Site 2) :
    wnd_signStep z u v = 1 ↔ (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 - 1 ∧ v 1 = z 1 := by
  classical
  unfold wnd_signStep
  constructor
  · intro h
    split_ifs at h with h1 h2 <;> first | exact h1 | (exfalso; revert h; decide)
  · intro h; simp only [if_pos h]


theorem wpd_signStep_down_iff (z u v : Site 2) :
    wnd_signStep z u v = -1 ↔ (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 ∧ v 1 = z 1 - 1 := by
  classical
  unfold wnd_signStep
  constructor
  · intro h
    split_ifs at h with h1 h2
    exact h2
  · intro h
    by_cases hup : (u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 - 1 ∧ v 1 = z 1
    · exfalso
      obtain ⟨_, hu1, _⟩ := hup
      obtain ⟨_, hu1', _⟩ := h
      rw [hu1'] at hu1; omega
    · simp only [if_neg hup, if_pos h]


theorem wpd_signStep_dichotomy (z u v : Site 2) (h : wnd_signStep z u v ≠ 0) :
    ((u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 - 1 ∧ v 1 = z 1) ∨
    ((u 0 = v 0 ∧ u 0 ≤ z 0 - 1) ∧ u 1 = z 1 ∧ v 1 = z 1 - 1) := by
  rcases wnd_signStep_mem z u v with h1 | h1 | h1
  · exact Or.inl ((wpd_signStep_up_iff z u v).mp h1)
  · exact absurd h1 h
  · exact Or.inr ((wpd_signStep_down_iff z u v).mp h1)


theorem wpd_count_le_one_of_nodup {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hnd : Vc.edges.Nodup) (e : Sym2 (Site 2)) :
    Vc.edges.count e ≤ 1 := by
  exact List.nodup_iff_count_le_one.mp hnd e


theorem wpd_simple_cross_le_one {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) (z : Site 2) (c : ℤ) :
    Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2)) ≤ 1 :=
  wpd_count_le_one_of_nodup Vc hcyc.edges_nodup _


theorem wpd_simple_cross_iff {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (hcyc : Vc.IsCycle) (z : Site 2) (c : ℤ) :
    wis_ind z Vc (c + 1) ≠ wis_ind z Vc c ↔
      Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2)) = 1 := by
  rw [wis_ind_step_neq_iff z Vc c]
  constructor
  · intro hodd
    have hle := wpd_simple_cross_le_one Vc hcyc z c
    rw [Nat.odd_iff] at hodd
    omega
  · intro h1; rw [h1]; exact odd_one


end Lattice
end StatMech
