/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Def.StatisticalMechanics.Code.Universality.HexEndpointCriticalDivergence.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

namespace HexEndpointSideFibers

theorem sidePred_height_unique {a : ℂ} {h0 : ℤ}
    (S : HexEndpointSideFibers a h0) (T L L' : ℕ) (ts : List ℤ)
    (hL : S.sidePred T L ts) (hL' : S.sidePred T L' ts) : L = L' := by
  obtain ⟨i, hiL, hits⟩ := hL
  obtain ⟨j, hjL, hjts⟩ := hL'
  have hij : i = j := S.turns_injective T (hits.trans hjts.symm)
  subst j
  exact hiL.symm.trans hjL

end HexEndpointSideFibers
end
end StatMech.Universality
