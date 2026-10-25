/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualPrefactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardRibbonIdentification.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.SimpleGraphCellularRibbonEmbedding.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialDualPrefactor.Part2


namespace StatMech.FrontierA

open Finset

open scoped BigOperators


variable {E : Type*} [Fintype E] [DecidableEq E]

structure KacWardSubgraphCoefficientIdentification
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (coefficient : Finset E -> Complex) (kacWard : Matrix Q Q Complex)
    (weight : E -> Complex) (prefactor : Complex) where
  permutationEdgeSet : Equiv.Perm Q -> Finset E
  coefficientFiber : forall F : Finset E,
    (∑ sigma : finiteMapFiber permutationEdgeSet F,
        matrixDetPermutationTerm (1 - kacWard) sigma.1) =
      prefactor * (coefficient F * ∏ edge ∈ F, weight edge)


structure RibbonDualBoundaryIdentification
    {Dprimal Ddual : Type*}
    [Fintype Dprimal] [DecidableEq Dprimal]
    [Fintype Ddual] [DecidableEq Ddual]
    (primalRibbon : RibbonPermutationSystem E Dprimal)
    (dualRibbon : RibbonPermutationSystem E Ddual) where
  boundaryEquiv : forall F : Finset E,
    Fin (dualRibbon.boundaryComponents F) ≃
      Fin (primalRibbon.boundaryComponents Fᶜ)

end StatMech.FrontierA
