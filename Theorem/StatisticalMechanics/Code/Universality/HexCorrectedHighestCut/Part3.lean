/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedHighestCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedCriticalDivergence
import Def.StatisticalMechanics.Code.Universality.HexCorrectedHighestCut.Part2


namespace StatMech.Universality

open HexWalk

noncomputable section

namespace HexCSHighestCut

variable {T : ℕ} {hT : 1 ≤ T}


theorem recurrence (H : HexCSHighestCut T hT)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    hexCSInfiniteSideMassAtWidth (T + 1) -
        hexCSInfiniteSideMassAtWidth T ≤
      hexChiE⁻¹ * (hexCSInfiniteTopMassAtWidth (T + 1)) ^ 2 := by
  have hbound := (H.toHighestCut hwalk).recursion_bound
    (le_of_lt hexChiE_inv_pos)
  rw [show (∑' d, (H.toHighestCut hwalk).wtγ d) =
      hexCSInfiniteSideMassAtWidth (T + 1) -
        hexCSInfiniteSideMassAtWidth T from
      hexCSNewSide_tsum_eq_difference T hT hwalk,
    show (∑' b, (H.toHighestCut hwalk).wtB b) =
      hexCSInfiniteTopMassAtWidth (T + 1) from
      hexCSNextTop_tsum_eq_mass T hT] at hbound
  exact hbound

end HexCSHighestCut


theorem hexCS_highestCuts_recurrence
    (HC : ∀ T (hT : 1 ≤ T), HexCSHighestCut T hT)
    (hwalk : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE)) :
    ∀ T, 1 ≤ T →
      hexCSInfiniteSideMassAtWidth (T + 1) -
          hexCSInfiniteSideMassAtWidth T ≤
        hexChiE⁻¹ * (hexCSInfiniteTopMassAtWidth (T + 1)) ^ 2 := by
  intro T hT
  exact (HC T hT).recurrence hwalk

end
end StatMech.Universality
