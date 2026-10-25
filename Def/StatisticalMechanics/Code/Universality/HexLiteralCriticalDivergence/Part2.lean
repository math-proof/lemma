/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCoefficientAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexColumnMembershipClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Structure.StatisticalMechanics.Code.Universality.HexLiteralCriticalDivergence


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HexLiteralSideFibers

noncomputable def columnEmb {a : ℂ} {h0 : ℤ}
    (S : HexLiteralSideFibers a h0) (T : ℕ) :
    HexColumnEmb (List ℤ) (S.Index T) where
  wtSAW := hexSAWwt a h0 hexChiE
  emb := S.turns T
  emb_inj := S.turns_injective T
  wtSAW_nn := hexSAWwt_nonneg a h0 (le_of_lt hexChiE_pos)
  scale := S.height T


def sidePred {a : ℂ} {h0 : ℤ} (S : HexLiteralSideFibers a h0)
    (T L : ℕ) (ts : List ℤ) : Prop :=
  ∃ i : S.Index T, S.height T i = L ∧ S.turns T i = ts


end HexLiteralSideFibers
end StatMech.Universality
