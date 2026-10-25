/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3


namespace StatMech.Universality

open HexWalk

noncomputable section

noncomputable def hexEndpointColumnEmbOfPred
    (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 ≤ x)
    (P : List ℤ → Prop) (scale : {ts : List ℤ // P ts} → ℕ) :
    HexColumnEmb (List ℤ) {ts : List ℤ // P ts} where
  wtSAW := hexEndpointSAWwt a h0 x
  emb := fun s => s.1
  emb_inj := Subtype.val_injective
  wtSAW_nn := hexEndpointSAWwt_nonneg a h0 hx
  scale := scale


noncomputable def hecd_columnSum
    (a : ℂ) (h0 : ℤ) (P : List ℤ → Prop)
    (scale : {ts : List ℤ // P ts} → ℕ) (v : ℕ) : ℝ :=
  (hexEndpointColumnEmbOfPred a h0 (le_of_lt hexChiE_pos) P scale).fiberSum v

end
end StatMech.Universality
