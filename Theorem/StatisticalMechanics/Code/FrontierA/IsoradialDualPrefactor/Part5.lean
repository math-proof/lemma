/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part4


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

namespace KacWardSubgraphCoefficientIdentification

theorem expansion
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (coefficient : Finset E -> Complex) (kacWard : Matrix Q Q Complex)
    (weight : E -> Complex) (prefactor : Complex)
    (I : KacWardSubgraphCoefficientIdentification
      coefficient kacWard weight prefactor) :
    (1 - kacWard).det =
      prefactor * kwDualSubgraphSum coefficient weight := by
  rw [matrix_det_eq_sum_permutationTerm]
  calc
    (∑ sigma : Equiv.Perm Q,
        matrixDetPermutationTerm (1 - kacWard) sigma) =
      ∑ F : Finset E,
        ∑ sigma : finiteMapFiber I.permutationEdgeSet F,
          matrixDetPermutationTerm (1 - kacWard) sigma.1 :=
      (Fintype.sum_fiberwise I.permutationEdgeSet
        (matrixDetPermutationTerm (1 - kacWard))).symm
    _ = prefactor * kwDualSubgraphSum coefficient weight := by
      unfold kwDualSubgraphSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro F _
      rw [I.coefficientFiber F]

end KacWardSubgraphCoefficientIdentification
end StatMech.FrontierA
