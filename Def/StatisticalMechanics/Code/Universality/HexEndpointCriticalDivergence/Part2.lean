/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Structure.StatisticalMechanics.Code.Universality.HexEndpointCriticalDivergence


namespace StatMech.Universality

open HexWalk

noncomputable section

namespace HexEndpointSideFibers

noncomputable def columnEmb {a : ℂ} {h0 : ℤ}
    (S : HexEndpointSideFibers a h0) (T : ℕ) :
    HexColumnEmb (List ℤ) (S.Index T) where
  wtSAW := hexEndpointSAWwt a h0 hexChiE
  emb := S.turns T
  emb_inj := S.turns_injective T
  wtSAW_nn := hexEndpointSAWwt_nonneg a h0 (le_of_lt hexChiE_pos)
  scale := S.height T

def sidePred {a : ℂ} {h0 : ℤ} (S : HexEndpointSideFibers a h0)
    (T L : ℕ) (ts : List ℤ) : Prop :=
  ∃ i : S.Index T, S.height T i = L ∧ S.turns T i = ts

end HexEndpointSideFibers
end
end StatMech.Universality
