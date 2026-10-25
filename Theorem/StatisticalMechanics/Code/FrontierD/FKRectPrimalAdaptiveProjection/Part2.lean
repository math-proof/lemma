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
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem fkRectPrimalFullExploredVertex_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) (v : R.Vertex) :
    FKRectPrimalFullExploredVertex R S rho v ↔
      FKRectPrimalExploredVertex R S (fkRectCutConfigOfFull R rho).1 v := by
  have hclosed := (fkRectCutConfigOfFull R rho).2
  have hforce : fkRectForceCutClosed R (fkRectCutConfigOfFull R rho).1 =
      (fkRectCutConfigOfFull R rho).1 := hclosed
  unfold FKRectPrimalFullExploredVertex FKRectPrimalExploredVertex
  rw [hforce, fkRectOpenGraph_cutConfigOfFull]


theorem mem_fkRectPrimalUnexploredPairEdges_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) (e : Sym2 R.Vertex) :
    e ∈ fkRectPrimalUnexploredPairEdges R S eta ↔
      ∃ x y : R.Vertex, e = s(x, y) ∧
        ¬ FKRectPrimalExploredVertex R S eta x ∧
        ¬ FKRectPrimalExploredVertex R S eta y := by
  rw [fkRectPrimalUnexploredPairEdges, FK.ocd_mem_innerEdgeFinset]
  constructor
  · rintro ⟨edge, rfl⟩
    induction edge using Sym2.ind with
    | _ x y =>
      exact ⟨x.1, y.1, FK.ocd_innerEdge_mk _ x y,
        x.2, y.2⟩
  · rintro ⟨x, y, rfl, hx, hy⟩
    let x' : FKRectPrimalUnexploredVertex R S eta := ⟨x, hx⟩
    let y' : FKRectPrimalUnexploredVertex R S eta := ⟨y, hy⟩
    refine ⟨s(x', y'), ?_⟩
    exact FK.ocd_innerEdge_mk _ x' y'


end
end StatMech.FrontierD
