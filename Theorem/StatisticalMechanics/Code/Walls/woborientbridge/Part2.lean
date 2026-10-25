/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/woborientbridge.lean -/

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
import Def.StatisticalMechanics.Code.Walls.woborientbridge
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

open StatMech.Walls


theorem wob_indJump_mem (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (c : ℤ) :
    wob_indJump z Vc c = 1 ∨ wob_indJump z Vc c = 0 ∨ wob_indJump z Vc c = -1 := by
  unfold wob_indJump
  rcases wis_ind_in_01 z Vc (c + 1) with h1 | h1 <;>
    rcases wis_ind_in_01 z Vc c with h0 | h0 <;> rw [h1, h0] <;> simp


theorem wob_indJump_ne_zero_iff (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a)
    (c : ℤ) :
    wob_indJump z Vc c ≠ 0 ↔ Odd (Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2))) := by
  unfold wob_indJump
  rw [sub_ne_zero, wis_ind_step_neq_iff z Vc c]


theorem wob_indJump_parity (z : Site 2) {a : Site 2} (Vc : (hypercubicLattice 2).Walk a a) (c : ℤ) :
    wob_indJump z Vc c % 2 =
      (if Odd (Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2))) then (1 : ℤ) else 0) % 2 := by
  by_cases hodd : Odd (Vc.edges.count (rpc_hCrossEdge (![c, z 1] : Site 2)))
  · rw [if_pos hodd]
    have hne : wob_indJump z Vc c ≠ 0 := (wob_indJump_ne_zero_iff z Vc c).mpr hodd
    rcases wob_indJump_mem z Vc c with h | h | h
    · rw [h]
    · exact absurd h hne
    · rw [h]; decide
  · rw [if_neg hodd]
    have h0 : wob_indJump z Vc c = 0 := by
      by_contra hc; exact hodd ((wob_indJump_ne_zero_iff z Vc c).mp hc)
    rw [h0]


end Lattice
end StatMech
