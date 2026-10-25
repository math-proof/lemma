/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas
import Structure.StatisticalMechanics.Code.FrontierA.IsoradialKacWardMetricClosure
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

variable {E D Q : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]


namespace IsoradialMetricPermutationExpansion

def toCoefficientIdentification
    {Vertex : Type*} [Fintype Vertex]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (theta : E -> Real)
    (exceptional : Vertex -> Bool)
    (data : IsoradialMetricPermutationExpansion
      R character kacWard theta exceptional) :
    CriticalKacWardRibbonCoefficientIdentification
      R character kacWard theta exceptional where
  permutationEdgeSet := data.permutationEdgeSet
  coefficientFiber := by
    intro F
    calc
      (∑ sigma : finiteMapFiber data.permutationEdgeSet F,
          matrixDetPermutationTerm (1 - kacWard) sigma.1) =
          ∑ sigma : finiteMapFiber data.permutationEdgeSet F,
            criticalKacWardRibbonPrefactor theta exceptional *
              data.normalizedTerm sigma.1 := by
        apply Finset.sum_congr rfl
        intro sigma _
        exact data.permutationTerm_eq sigma.1
      _ = criticalKacWardRibbonPrefactor theta exceptional *
          ∑ sigma : finiteMapFiber data.permutationEdgeSet F,
            data.normalizedTerm sigma.1 := by
        rw [Finset.mul_sum]
      _ = _ := by rw [data.normalizedFiber F]

end IsoradialMetricPermutationExpansion
end StatMech.FrontierA
