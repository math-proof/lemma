/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexW2Cut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexWall3.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraDisplacement.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexInfraCut
import Theorem.StatisticalMechanics.Code.Universality.HexSurgerySeams.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexW2Cut.Part4


namespace StatMech.Universality

open HexWalk List Filter

open scoped BigOperators Real


noncomputable def hexW2_highestCut (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 < x)
    (memD : List ℤ → Prop)
    (B : Type)
    (wtB : B → ℝ) (wtB_nn : ∀ b, 0 ≤ wtB b)
    (split : {ts // memD ts} → B × B)
    (hwtB1 : ∀ d, wtB (split d).1 = hexSAWwt a h0 x (d.1.take (hexW2_cutPos h0 d.1)))
    (hwtB2 : ∀ d, wtB (split d).2 =
      hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
        (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1)))
    (split_inj : Function.Injective split)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1))
    (hBsum : Summable wtB) :
    HexHighestCut x⁻¹ :=
  hexHighestCutClosed a h0 hx memD B wtB wtB_nn
    (fun d => hexW2_cutPos h0 d.1)
    (fun d => hexW2_cutPos_le h0 d.1)
    split hwtB1 hwtB2 split_inj hDsum hBsum


noncomputable def hexW2_highestCut_chi (a : ℂ) (h0 : ℤ)
    (memD : List ℤ → Prop)
    (B : Type)
    (wtB : B → ℝ) (wtB_nn : ∀ b, 0 ≤ wtB b)
    (split : {ts // memD ts} → B × B)
    (hwtB1 : ∀ d, wtB (split d).1 = hexSAWwt a h0 hexChiE (d.1.take (hexW2_cutPos h0 d.1)))
    (hwtB2 : ∀ d, wtB (split d).2 =
      hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
        (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) hexChiE (d.1.drop (hexW2_cutPos h0 d.1)))
    (split_inj : Function.Injective split)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable wtB) :
    HexHighestCut hexChiE⁻¹ :=
  hexW2_highestCut a h0 hexChiE_pos memD B wtB wtB_nn split hwtB1 hwtB2 split_inj hDsum hBsum

end StatMech.Universality
