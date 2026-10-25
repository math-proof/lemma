/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptiveProjection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalWitnessStep.Part2
import Theorem.StatisticalMechanics.Code.Probability.AdaptiveFibreStep
import Theorem.StatisticalMechanics.Code.FK.FKDisjointBoxDomainMarkov.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part4
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


def FKRectPrimalFullCrossingSource
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex))
    (i : Fin R.height) : Prop :=
  ∃ z : Fin R.height,
    (FK.openSub (fkRectCutGraph R) rho).Reachable
      (fkRectLeftColumn R, i) (fkRectRightColumn R, z)


def FKRectPrimalFullDistinctCrossingWitness
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) : Prop :=
  (∀ i ∈ S, FKRectPrimalFullCrossingSource R rho i) ∧
  (∀ i ∈ S, ∀ j ∈ S, i ≠ j →
    ¬ (FK.openSub (fkRectCutGraph R) rho).Reachable
      (fkRectLeftColumn R, i) (fkRectLeftColumn R, j))


end
end StatMech.FrontierD
