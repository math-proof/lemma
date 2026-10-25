/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardMetricClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardPolygonalDevelopment.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardAtlas
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

universe u

variable {E D Q : Type*} [Fintype E] [DecidableEq E]
  [Fintype D] [DecidableEq D] [Fintype Q] [DecidableEq Q]


structure IsoradialMetricPermutationExpansion
    {Vertex : Type*} [Fintype Vertex]
    (R : RibbonPermutationSystem E D)
    (character : forall F : Finset E,
      Fin (R.boundaryComponents F) -> Complex)
    (kacWard : Matrix Q Q Complex) (theta : E -> Real)
    (exceptional : Vertex -> Bool) where
  permutationEdgeSet : Equiv.Perm Q -> Finset E
  normalizedTerm : Equiv.Perm Q -> Complex
  permutationTerm_eq : forall sigma,
    matrixDetPermutationTerm (1 - kacWard) sigma =
      criticalKacWardRibbonPrefactor theta exceptional * normalizedTerm sigma
  normalizedFiber : forall F : Finset E,
    (∑ sigma : finiteMapFiber permutationEdgeSet F,
      normalizedTerm sigma.1) =
        ribbonBoundaryCharacterCoefficient R character F *
          ∏ edge ∈ F, isoradialCriticalMu (theta edge)

end StatMech.FrontierA
