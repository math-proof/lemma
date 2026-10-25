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
import Def.StatisticalMechanics.Code.Exact3D.ComponentThirdSplit.Part21
open Filter
open scoped symmDiff


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_sourceClassSupportBudget
    (hbudget :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackSourceClassSupportBudgetWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hbudget β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  rcases hn H hH Ω v hv with
    ⟨coefficientBudget, hcase, htotal⟩
  have hcoeff :
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v ≤
        ∑ S ∈ sourceClassSupport, coefficientBudget S := by
    calc
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
          β H n Ωnz v =
        ∑ S ∈ sourceClassSupport,
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
            β H n Ωnz v S := by
        simpa [sourceClassSupport] using
          finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_sum
            β H n Ωnz v
      _ ≤ ∑ S ∈ sourceClassSupport, coefficientBudget S :=
        Finset.sum_le_sum (fun S hS => hcase S hS)
  exact hcoeff.trans htotal

set_option linter.style.longLine false in


theorem sourceClassSupportBudget_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack
    (hslack :
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical) :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackSourceClassSupportBudgetWeightNonzeroPositiveSubcritical := by
  intro β hβpos hβc
  filter_upwards [hslack β hβpos hβc] with n hn
  intro H hH Ω v hv
  let Ωnz := finiteBoundaryGhostWeightNonzeroCutoff β H n Ω
  let sourceClassSupport :=
    finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSupport
      n Ωnz v
  refine
    ⟨fun S =>
      finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
        β H n Ωnz v S, ?_, ?_⟩
  · intro S _hS
    exact le_rfl
  · have hslackv :
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v ≤
          finiteBoundaryGhostBoundaryFiberSourcePairVertexProfile
              β H n Ωnz v -
            finiteBoundaryGhostDecrementedSourceWeightVertexSigmaSourceActiveContribution
              β H n Ωnz v := by
      simpa [Ωnz] using hn H hH Ω v hv
    have hsum :
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum
            β H n Ωnz v =
          ∑ S ∈ sourceClassSupport,
            finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientSourceClassSum
              β H n Ωnz v S := by
      simpa [sourceClassSupport] using
        finiteBoundaryGhostSourceInactiveNonTwoPointClassifiedCoefficientWeightSum_eq_sourceClassSupport_sum
          β H n Ωnz v
    simpa [hsum]
      using hslackv

set_option linter.style.longLine false in


theorem inactiveNonTwoPointClassifiedCoefficientProfileSlackSourceClassSupportBudget_iff_profileSlack :
    BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackSourceClassSupportBudgetWeightNonzeroPositiveSubcritical ↔
      BoundaryVertexDecrementedSourceInactiveNonTwoPointClassifiedCoefficientProfileSlackWeightNonzeroPositiveSubcritical :=
  ⟨inactiveNonTwoPointClassifiedCoefficientProfileSlack_of_sourceClassSupportBudget,
    sourceClassSupportBudget_of_inactiveNonTwoPointClassifiedCoefficientProfileSlack⟩

end Exact3D
end StatMech
