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
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part3


namespace StatMech.Universality

open HexWalk List Filter Topology

open scoped BigOperators Topology Real NNReal


noncomputable def hexWall3_HWDataRecon (a : ℂ) (h0 : ℤ) (c : ℕ → ℝ) (x : ℝ) (N : ℕ)
    (hx : 0 < x) (hlt : x < hexChiE)
    (hsum : ∀ T, Summable (fun w : {ts // hexWall3_mem a h0 T ts} =>
      hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices))
    (hle_one : ∀ T, (∑' w : {ts // hexWall3_mem a h0 T ts},
      hexChiE ^ (HexWalk.ofTurns a h0 w.1).numVertices) ≤ 1)
    (Dn : Type) [Fintype Dn]
    (wtγ : Dn → ℝ) (wtγ_nn : ∀ d, 0 ≤ wtγ d)
    (partial_eq : ∑ d, wtγ d = ∑ n ∈ Finset.range N, c n * x ^ n)
    (lower upper : Dn → List HexBridge)
    (hlo : ∀ d, StrictDecreasingWidths (lower d))
    (hup : ∀ d, StrictDecreasingWidths (upper d))
    (htwoEdge : ∀ d, wtγ d * x ^ 2
        = ((lower d).map (fun b => x ^ (HexWalk.ofTurns a h0 b.content).numVertices)).prod
          * ((upper d).map (fun b => x ^ (HexWalk.ofTurns a h0 b.content).numVertices)).prod)
    (hReachesLo : ∀ d, ∀ b ∈ lower d, hexWall3_ReachesWidth a h0 b.width b.content)
    (hSAWLo : ∀ d, ∀ b ∈ lower d, (HexWalk.ofTurns a h0 b.content).IsLegalSAW)
    (hReachesUp : ∀ d, ∀ b ∈ upper d, hexWall3_ReachesWidth a h0 b.width b.content)
    (hSAWUp : ∀ d, ∀ b ∈ upper d, (HexWalk.ofTurns a h0 b.content).IsLegalSAW)
    (decomp_inj : Function.Injective
      (fun d => (hbw_widthFinset (lower d), hbw_widthFinset (upper d)))) :
    HexHWDataRecon c
      (fun T => (hexWall3_column a h0 T hexChiE (hsum T) (hle_one T)).colSum x) x N :=
  let Col : ∀ T, HexColumn T hexChiE :=
    fun T => hexWall3_column a h0 T hexChiE (hsum T) (hle_one T)
  let υ : ℕ → ℝ := fun T => (Col T).colSum x
  have hυnn : ∀ T, 0 ≤ υ T := fun T => (Col T).colSum_nonneg (le_of_lt hx)
  have hυle : ∀ T, υ T ≤ (x / hexChiE) ^ T :=
    fun T => (Col T).colSum_le_pow (le_of_lt hx) hexChiE_pos (le_of_lt hlt)
  have hmul : Multipliable (fun T => 1 + υ T) :=
    hex_bridge_multipliable υ (hex_ups_summable υ x (le_of_lt hx) hlt hυnn hυle)
  hexHWDataClosed c υ x N hυnn hmul
    Dn wtγ wtγ_nn partial_eq
    (fun d => (hbw_widthFinset (lower d), hbw_widthFinset (upper d)))
    decomp_inj
    (fun d => hexWall3_weightBound_factor x (wtγ d) hx (lower d) (upper d) (hlo d) (hup d)
      υ (fun b => x ^ (HexWalk.ofTurns a h0 b.content).numVertices)
      (fun b hb =>
        hexWall3_colDomination_uncond a h0 b hexChiE (hsum b.width) (hle_one b.width)
          (le_of_lt hx) hexChiE_pos (le_of_lt hlt) (hReachesLo d b hb) (hSAWLo d b hb))
      (fun b hb =>
        hexWall3_colDomination_uncond a h0 b hexChiE (hsum b.width) (hle_one b.width)
          (le_of_lt hx) hexChiE_pos (le_of_lt hlt) (hReachesUp d b hb) (hSAWUp d b hb))
      (fun b => by positivity)
      (htwoEdge d))


end StatMech.Universality
