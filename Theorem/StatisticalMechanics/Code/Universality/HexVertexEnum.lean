/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexVertexEnum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexVertex.Part5


namespace StatMech.Universality

open Complex

open HexWalk


theorem hexPhase_eq_lambda_zpow (w : HexWalk) :
    Complex.exp (-Complex.I * ((5/8 : ℝ) : ℂ) * ((w.turning : ℝ) : ℂ))
      = hexLambda ^ (w.turnCount) := by
  unfold hexLambda
  rw [hexExpI_zpow]
  rw [turning]
  congr 1
  push_cast
  ring


theorem hexContribution_eq_paraf (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (z v : ℂ)
    (ts : List ℤ)
    (hcond : (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region
        ∧ (ofTurns a h0 ts).EndsAt z) :
    (z - v) * parafSummand region a h0 z (5/8) hexChi ts
      = hexContribution (z - v) ((ofTurns a h0 ts).turnCount)
          ((ofTurns a h0 ts).numVertices) := by
  unfold parafSummand hexContribution
  rw [if_pos hcond]
  rw [show ((hexChi : ℝ) : ℂ) = (hexChi : ℂ) from rfl]
  rw [← hexPhase_eq_lambda_zpow (ofTurns a h0 ts)]
  ring


theorem numVertices_concat (a : ℂ) (h0 t : ℤ) (ts : List ℤ) :
    (ofTurns a h0 (ts ++ [t])).numVertices = (ofTurns a h0 ts).numVertices + 1 := by
  simp [numVertices, ofTurns]


theorem turnCount_concat (a : ℂ) (h0 t : ℤ) (ts : List ℤ) :
    (ofTurns a h0 (ts ++ [t])).turnCount = (ofTurns a h0 ts).turnCount + t := by
  simp [turnCount, ofTurns, List.sum_append]


theorem turnCount_append_block (a : ℂ) (h0 : ℤ) (base block : List ℤ) :
    (ofTurns a h0 (base ++ block)).turnCount
      = (ofTurns a h0 base).turnCount + block.sum := by
  simp [turnCount, ofTurns, List.sum_append]


theorem hexUnit_add_two (h : ℤ) : hexUnit (h + 2) = hexOmega * hexUnit h := by
  unfold hexUnit hexOmega
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring


theorem hexUnit_add_four (h : ℤ) : hexUnit (h + 4) = hexOmega ^ 2 * hexUnit h := by
  rw [show (h + 4 : ℤ) = (h + 2) + 2 by ring, hexUnit_add_two, hexUnit_add_two]
  ring


theorem genuine_triplet_zero (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (ts : List ℤ)
    (hp : (ofTurns a h0 ts).IsLegalSAW ∧ (ofTurns a h0 ts).StaysIn region
        ∧ (ofTurns a h0 ts).EndsAt (v + du))
    (hq : (ofTurns a h0 (ts ++ [-1])).IsLegalSAW
        ∧ (ofTurns a h0 (ts ++ [-1])).StaysIn region
        ∧ (ofTurns a h0 (ts ++ [-1])).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (ts ++ [1])).IsLegalSAW
        ∧ (ofTurns a h0 (ts ++ [1])).StaysIn region
        ∧ (ofTurns a h0 (ts ++ [1])).EndsAt (v + hexOmega ^ 2 * du)) :
    ((v + du) - v) * parafSummand region a h0 (v + du) (5/8) hexChi ts
      + ((v + hexOmega * du) - v)
          * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (ts ++ [-1])
      + ((v + hexOmega ^ 2 * du) - v)
          * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (ts ++ [1])
      = 0 := by
  rw [hexContribution_eq_paraf region a h0 (v + du) v ts hp,
      hexContribution_eq_paraf region a h0 (v + hexOmega * du) v (ts ++ [-1]) hq,
      hexContribution_eq_paraf region a h0 (v + hexOmega ^ 2 * du) v (ts ++ [1]) hr]
  
  rw [turnCount_concat a h0 (-1) ts, turnCount_concat a h0 1 ts,
      numVertices_concat a h0 (-1) ts, numVertices_concat a h0 1 ts]
  
  simp only [add_sub_cancel_left]
  
  have key := hexTripletContribution_zero du ((ofTurns a h0 ts).turnCount)
      ((ofTurns a h0 ts).numVertices)
  
  
  have e1 : ((ofTurns a h0 ts).turnCount + (-1 : ℤ)) = (ofTurns a h0 ts).turnCount - 1 := by
    ring
  rw [e1]
  exact key


theorem genuine_pair_zero (region : ℂ → Prop) (a : ℂ) (h0 : ℤ) (v du : ℂ)
    (base Lq Lr : List ℤ)
    (hLqsum : Lq.sum = -4) (hLrsum : Lr.sum = 4)
    (hlen : Lq.length = Lr.length)
    (hq : (ofTurns a h0 (base ++ Lq)).IsLegalSAW
        ∧ (ofTurns a h0 (base ++ Lq)).StaysIn region
        ∧ (ofTurns a h0 (base ++ Lq)).EndsAt (v + hexOmega * du))
    (hr : (ofTurns a h0 (base ++ Lr)).IsLegalSAW
        ∧ (ofTurns a h0 (base ++ Lr)).StaysIn region
        ∧ (ofTurns a h0 (base ++ Lr)).EndsAt (v + hexOmega ^ 2 * du)) :
    ((v + hexOmega * du) - v)
        * parafSummand region a h0 (v + hexOmega * du) (5/8) hexChi (base ++ Lq)
      + ((v + hexOmega ^ 2 * du) - v)
          * parafSummand region a h0 (v + hexOmega ^ 2 * du) (5/8) hexChi (base ++ Lr)
      = 0 := by
  rw [hexContribution_eq_paraf region a h0 (v + hexOmega * du) v (base ++ Lq) hq,
      hexContribution_eq_paraf region a h0 (v + hexOmega ^ 2 * du) v (base ++ Lr) hr]
  
  rw [turnCount_append_block a h0 base Lq, turnCount_append_block a h0 base Lr,
      hLqsum, hLrsum]
  
  have hnq : (ofTurns a h0 (base ++ Lq)).numVertices
      = (ofTurns a h0 base).numVertices + Lq.length := by
    simp only [numVertices, ofTurns, List.length_append]; omega
  have hnr : (ofTurns a h0 (base ++ Lr)).numVertices
      = (ofTurns a h0 base).numVertices + Lr.length := by
    simp only [numVertices, ofTurns, List.length_append]; omega
  rw [hnq, hnr, ← hlen]
  simp only [add_sub_cancel_left]
  
  have key := hexPairContribution_zero du ((ofTurns a h0 base).turnCount)
      ((ofTurns a h0 base).numVertices + Lq.length)
  
  have e1 : ((ofTurns a h0 base).turnCount + (-4 : ℤ))
      = (ofTurns a h0 base).turnCount - 4 := by ring
  rw [e1]
  exact key


end StatMech.Universality
