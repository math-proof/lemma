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
import Def.StatisticalMechanics.Code.Universality.HexLiteralCriticalDivergence.Part2


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


namespace HexLiteralSideFibers

theorem sidePred_height_unique {a : ℂ} {h0 : ℤ}
    (S : HexLiteralSideFibers a h0) (T L L' : ℕ) (ts : List ℤ)
    (hL : S.sidePred T L ts) (hL' : S.sidePred T L' ts) : L = L' := by
  obtain ⟨i, hiL, hits⟩ := hL
  obtain ⟨j, hjL, hjts⟩ := hL'
  have hij : i = j := S.turns_injective T (hits.trans hjts.symm)
  subst j
  exact hiL.symm.trans hjL

end HexLiteralSideFibers
end StatMech.Universality
