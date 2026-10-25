/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamStableRawComponentForest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawHoleCollisionSplit.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamStableRawComponentForest.Part4
open Finset


namespace StatMech.GrahamGHS.FourColor

universe u v uI uW

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


attribute [instance]
  FiniteRelationMinimalTightProblem.stateFintype
  FiniteRelationMinimalTightProblem.stateDecidableEq
  FiniteRelationMinimalTightProblem.tokenFintype
  FiniteRelationMinimalTightProblem.tokenDecidableEq

noncomputable def finiteEmbedding_replaceAt
    {A : Type*} {size : Nat} (block : Fin size ↪ A) (extra : A)
    (hfresh : ∀ i, extra ≠ block i) (index : Fin size) : Fin size ↪ A where
  toFun i := if i = index then extra else block i
  inj' := by
    intro x y hxy
    by_cases hx : x = index
    · subst x
      by_cases hy : y = index
      · exact hy.symm
      · exfalso
        apply hfresh y
        simpa only [if_pos, if_neg, hy] using hxy
    · by_cases hy : y = index
      · subst y
        exfalso
        apply hfresh x
        simpa only [if_pos, if_neg, hx] using hxy.symm
      · exact block.injective (by
          simpa only [if_neg, hx, hy] using hxy)

end StatMech.GrahamGHS.FourColor
