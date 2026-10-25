/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRecon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon


namespace StatMech.Universality

open Filter Topology Complex

open scoped Topology BigOperators


noncomputable def hexHighestCutRecon (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 < x)
    (memD : List ℤ → Prop)
    (B : Type)
    (wtB : B → ℝ) (wtB_nn : ∀ b, 0 ≤ wtB b)
    (cpos : {ts // memD ts} → ℕ)
    (a2 : {ts // memD ts} → ℂ) (h2 : {ts // memD ts} → ℤ)
    (hcp : ∀ d : {ts // memD ts}, cpos d ≤ d.1.length)
    (hleg1 : ∀ d : {ts // memD ts}, (HexWalk.ofTurns a h0 d.1).IsLegalSAW →
      (HexWalk.ofTurns a h0 (d.1.take (cpos d))).IsLegalSAW)
    (hleg2 : ∀ d : {ts // memD ts}, (HexWalk.ofTurns a h0 d.1).IsLegalSAW →
      (HexWalk.ofTurns (a2 d) (h2 d) (d.1.drop (cpos d))).IsLegalSAW)
    (split : {ts // memD ts} → B × B)
    (hwtB1 : ∀ d, wtB (split d).1 = hexSAWwt a h0 x (d.1.take (cpos d)))
    (hwtB2 : ∀ d, wtB (split d).2 = hexSAWwt (a2 d) (h2 d) x (d.1.drop (cpos d)))
    (split_inj : Function.Injective split)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1))
    (hBsum : Summable wtB) :
    HexHighestCut x⁻¹ where
  D := {ts // memD ts}
  B := B
  wtγ := fun d => hexSAWwt a h0 x d.1
  wtB := wtB
  wtB_nn := wtB_nn
  wtγ_nn := fun d => hexSAWwt_nonneg a h0 (le_of_lt hx) d.1
  split := split
  split_inj := split_inj
  weight_bound := by
    intro d
    rw [hwtB1 d, hwtB2 d]
    exact hexHighestCut_weight_bound_literal a (a2 d) h0 (h2 d) x hx d.1 (cpos d)
      (hcp d) (hleg1 d) (hleg2 d)
  D_summable := hDsum
  B_summable := hBsum


end StatMech.Universality
