/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW1ExitGeom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
import Theorem.StatisticalMechanics.Code.Universality.HexInfraHeading
import Theorem.StatisticalMechanics.Code.Universality.HexW1Sides.Part3
import Def.StatisticalMechanics.Code.Universality.HexW1ExitGeom.Part2


namespace StatMech.Universality

open HexWalk List Complex

open scoped BigOperators Real


theorem hexW1Exit_singleton_inner_eq (a : ℂ) (h0 : ℤ) :
    a - HexWalk.halfStep ((h0 + 3 : ℤ)) = a + HexWalk.halfStep h0 := by
  rw [hexW1Exit_halfStep_add_three]; ring


theorem hexW1Exit_mids_singleRight (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 [(-1 : ℤ)]).mids
      = [a, a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))] := by
  unfold HexWalk.ofTurns HexWalk.mids; simp [HexWalk.midsAux]


theorem hexW1Exit_singleRight_legal (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 [(-1 : ℤ)]).IsLegalSAW := by
  refine ⟨?_, ?_⟩
  · intro t ht; simp only [HexWalk.ofTurns_turns, List.mem_singleton] at ht; exact Or.inr ht
  · unfold HexWalk.IsSAW HexWalk.vertices HexWalk.ofTurns
    simp only [HexWalk.verticesAux]
    rw [List.nodup_cons]
    refine ⟨?_, List.nodup_singleton _⟩
    simp only [List.mem_singleton]
    intro heq
    have h2 : (2 : ℂ) * HexWalk.halfStep (h0 + (-1)) = 0 := by linear_combination -heq
    rcases mul_eq_zero.mp h2 with h | h
    · norm_num at h
    · exact hexW1Exit_halfStep_ne_zero (h0 + (-1)) h


theorem hexW1Exit_singleRight_endsAt (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 [(-1 : ℤ)]).EndsAt
      (a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) := by
  unfold HexWalk.EndsAt HexWalk.endMid HexWalk.ofTurns HexWalk.mids; simp [HexWalk.midsAux]


theorem hexW1Exit_singleRight_staysIn (a : ℂ) (h0 : ℤ) :
    (HexWalk.ofTurns a h0 [(-1 : ℤ)]).StaysIn
      (fun m => m = a ∨ m = a + HexWalk.halfStep h0 + HexWalk.halfStep (h0 + (-1))) := by
  intro m hm
  rw [hexW1Exit_mids_singleRight] at hm
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  exact hm


end StatMech.Universality
