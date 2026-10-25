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
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part3
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem mem_fkRectPrimalFullUnexploredPairEdges_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) (e : Sym2 R.Vertex) :
    e ∈ fkRectPrimalFullUnexploredPairEdges R S rho ↔
      ∃ x y : R.Vertex, e = s(x, y) ∧
        ¬ FKRectPrimalFullExploredVertex R S rho x ∧
        ¬ FKRectPrimalFullExploredVertex R S rho y := by
  classical
  simp [fkRectPrimalFullUnexploredPairEdges]


theorem fkRectPrimalFullUnexploredPairEdges_eq_decoded
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectPrimalFullUnexploredPairEdges R S rho =
      fkRectPrimalUnexploredPairEdges R S (fkRectCutConfigOfFull R rho).1 := by
  ext e
  rw [mem_fkRectPrimalFullUnexploredPairEdges_iff,
    mem_fkRectPrimalUnexploredPairEdges_iff]
  constructor
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((fkRectPrimalFullExploredVertex_iff R S rho x).2 h),
      fun h => hy ((fkRectPrimalFullExploredVertex_iff R S rho y).2 h)⟩
  · rintro ⟨x, y, he, hx, hy⟩
    exact ⟨x, y, he,
      fun h => hx ((fkRectPrimalFullExploredVertex_iff R S rho x).1 h),
      fun h => hy ((fkRectPrimalFullExploredVertex_iff R S rho y).1 h)⟩


end
end StatMech.FrontierD
