/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexWall3.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexConnClosed
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeFull.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeWeight.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Def.StatisticalMechanics.Code.Universality.HexWall3.Part2


namespace StatMech.Universality

open HexWalk List Filter Topology

open scoped BigOperators Topology Real NNReal


theorem hexWall3_column_colSum (a : ℂ) (h0 : ℤ) (T : ℕ) (χ : ℝ)
    (hsummable hle_one) (y : ℝ) :
    (hexWall3_column a h0 T χ hsummable hle_one).colSum y
      = ∑' w : {ts // hexWall3_mem a h0 T ts},
          y ^ (HexWalk.ofTurns a h0 w.1).numVertices :=
  hexColumnOfWidth_colSum a h0 T χ (hexWall3_mem a h0 T)
    (hexWall3_mem_reaches a h0 T) hsummable hle_one y


theorem hexWall3_bridge_mem (a : ℂ) (h0 : ℤ) (b : HexBridge)
    (hReaches : hexWall3_ReachesWidth a h0 b.width b.content)
    (hSAW : (HexWalk.ofTurns a h0 b.content).IsLegalSAW) :
    hexWall3_mem a h0 b.width b.content :=
  ⟨b, rfl, rfl, hReaches, hSAW⟩


theorem hexWall3_colDomination_uncond (a : ℂ) (h0 : ℤ) (b : HexBridge) (χ : ℝ)
    (hsummable hle_one) {x : ℝ}
    (hx0 : 0 ≤ x) (hχ : 0 < χ) (hxχ : x ≤ χ)
    (hReaches : hexWall3_ReachesWidth a h0 b.width b.content)
    (hSAW : (HexWalk.ofTurns a h0 b.content).IsLegalSAW) :
    x ^ (HexWalk.ofTurns a h0 b.content).numVertices
      ≤ (hexWall3_column a h0 b.width χ hsummable hle_one).colSum x :=
  hexClosed_colDomination a h0 b.width χ (hexWall3_mem a h0 b.width)
    (hexWall3_mem_reaches a h0 b.width) hsummable hle_one
    hx0 hχ hxχ b.content (hexWall3_bridge_mem a h0 b hReaches hSAW)


theorem hexWall3_halfStep_re (h : ℤ) :
    (HexWalk.halfStep h).re = (1 / 2) * Real.cos (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) := by
  unfold HexWalk.halfStep hexUnit
  rw [show (Complex.I * ((Real.pi : ℂ) / 6 + (((h : ℝ)) : ℂ) * ((Real.pi : ℂ) / 3)))
        = ((Real.pi / 6 + (h : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
  have h1 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  have h2 : ((1 : ℂ) / 2).im = 0 := by norm_num
  rw [h1, h2]; ring


theorem hexWall3_reachesWidth_witness (a : ℂ) :
    hexWall3_ReachesWidth a 0 1 [(-1 : ℤ)] := by
  refine ⟨a + HexWalk.halfStep 0 + HexWalk.halfStep (0 + (-1)) + HexWalk.halfStep (0 + (-1)),
    ?_, ?_⟩
  · unfold HexWalk.ofTurns HexWalk.vertices
    rw [HexWalk.verticesAux_cons, HexWalk.verticesAux_nil]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    right; trivial
  · simp only [Complex.add_re, Nat.cast_one]
    rw [show (0 : ℤ) + (-1) = -1 by ring, hexWall3_halfStep_re, hexWall3_halfStep_re]
    have e0 : Real.pi / 6 + ((0 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 6 := by push_cast; ring
    have em1 : Real.pi / 6 + ((-1 : ℤ) : ℝ) * (Real.pi / 3) = -(Real.pi / 6) := by
      push_cast; ring
    rw [e0, em1, Real.cos_neg, Real.cos_pi_div_six]
    have hs3 : (4 : ℝ) / 3 ≤ Real.sqrt 3 := by
      rw [show (4 : ℝ) / 3 = Real.sqrt ((4 / 3) ^ 2) by rw [Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [hs3]


theorem hexWall3_isLegalSAW_witness (a : ℂ) :
    (HexWalk.ofTurns a 0 [(-1 : ℤ)]).IsLegalSAW := by
  constructor
  · intro t ht
    simp only [HexWalk.ofTurns, List.mem_singleton] at ht
    right; exact ht
  · unfold HexWalk.IsSAW HexWalk.ofTurns HexWalk.vertices
    rw [HexWalk.verticesAux_cons, HexWalk.verticesAux_nil, List.nodup_cons]
    refine ⟨?_, List.nodup_singleton _⟩
    simp only [List.mem_singleton]
    intro hcontra
    have hhs : HexWalk.halfStep (0 + (-1)) ≠ 0 := by
      unfold HexWalk.halfStep
      simp only [ne_eq, mul_eq_zero, not_or]
      exact ⟨by norm_num, hexUnit_ne_zero _⟩
    apply hhs
    have htwo : (2 : ℂ) * HexWalk.halfStep (0 + (-1)) = 0 := by linear_combination -hcontra
    rcases mul_eq_zero.mp htwo with h | h
    · exact absurd h (by norm_num)
    · exact h


end StatMech.Universality
