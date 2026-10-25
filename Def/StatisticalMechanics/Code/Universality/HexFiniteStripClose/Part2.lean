/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexFiniteStripClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexFiniteStripClose


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


noncomputable def hfs_hexHighestCutReconLegal (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 < x)
    (memD : List ℤ → Prop)
    (B : Type)
    (wtB : B → ℝ) (wtB_nn : ∀ b, 0 ≤ wtB b)
    (cpos : {ts // memD ts} → ℕ)
    (hcp : ∀ d : {ts // memD ts}, cpos d ≤ d.1.length)
    (split : {ts // memD ts} → B × B)
    (hwtB1 : ∀ d, wtB (split d).1 = hexSAWwt a h0 x (d.1.take (cpos d)))
    (hwtB2 : ∀ d, wtB (split d).2 = hexSAWwt
      (hfs_stMid a h0 (d.1.take (cpos d))) (hfs_stHead h0 (d.1.take (cpos d)))
      x (d.1.drop (cpos d)))
    (split_inj : Function.Injective split)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1))
    (hBsum : Summable wtB) :
    HexHighestCut x⁻¹ :=
  hexHighestCutRecon a h0 hx memD B wtB wtB_nn cpos
    (fun d => hfs_stMid a h0 (d.1.take (cpos d)))
    (fun d => hfs_stHead h0 (d.1.take (cpos d)))
    hcp
    (fun d hd => hfs_isLegalSAW_take a h0 d.1 (cpos d) hd)
    (fun d hd => hfs_isLegalSAW_drop a h0 d.1 (cpos d) (hcp d) hd)
    split hwtB1 hwtB2 split_inj hDsum hBsum


end StatMech.Universality
