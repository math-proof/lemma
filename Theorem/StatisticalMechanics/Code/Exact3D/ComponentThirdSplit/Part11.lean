/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/ComponentThirdSplit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteCombinatorics
import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc7componenteven
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part10
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassCardinalityCase_eq_zero_iff_card_eq_zero
    {n : ℕ}
    (S : Finset (Option (FK.boxVerts 3 n))) :
    finiteBoundaryGhostSourceClassCardinalityCase S =
        SourceClassCardinalityCase.zero ↔
      S.card = 0 := by
  unfold finiteBoundaryGhostSourceClassCardinalityCase
  by_cases hzero : S.card = 0
  · simp [hzero]
  · by_cases htwo : S.card = 2
    · simp [htwo]
    · simp [hzero, htwo]

set_option linter.style.longLine false in

theorem finiteBoundaryGhostSourceClassCardinalityCase_eq_two_iff_card_eq_two
    {n : ℕ}
    (S : Finset (Option (FK.boxVerts 3 n))) :
    finiteBoundaryGhostSourceClassCardinalityCase S =
        SourceClassCardinalityCase.two ↔
      S.card = 2 := by
  unfold finiteBoundaryGhostSourceClassCardinalityCase
  by_cases hzero : S.card = 0
  · simp [hzero]
  · by_cases htwo : S.card = 2
    · simp [htwo]
    · simp [hzero, htwo]

set_option linter.style.longLine false in


theorem finiteBoundaryGhostSourceClassCardinalityCase_fourPlus_card_ge_four_of_sourceClassSupport
    {n : ℕ}
    {Ω : Finset
      (↥(Sharpness.withGhost (FK.boxGraph 3 n)).edgeFinset → ℕ)}
    {v : FK.boxVerts 3 n}
    {S : Finset (Option (FK.boxVerts 3 n))}
    (hS :
      S ∈
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
          n Ω v)
    (hcase :
      finiteBoundaryGhostSourceClassCardinalityCase S =
        SourceClassCardinalityCase.fourPlus) :
    4 ≤ S.card := by
  rcases
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport_card_eq_zero_or_two_or_four_le
      hS with hzero | htwo | hfour
  · exfalso
    simp [finiteBoundaryGhostSourceClassCardinalityCase, hzero] at hcase
  · exfalso
    simp [finiteBoundaryGhostSourceClassCardinalityCase, htwo] at hcase
  · exact hfour


end Exact3D
end StatMech
