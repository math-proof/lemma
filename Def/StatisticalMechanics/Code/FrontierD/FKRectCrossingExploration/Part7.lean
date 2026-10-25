/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCrossingExploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalDualCrossings.Part7
import Theorem.StatisticalMechanics.Code.Probability.FiniteWitnessUnionBound
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreFreeDomination.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part6


namespace StatMech.FrontierD

noncomputable section

def fkRectPrimalExplorationOutsideOpenGraph
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) : SimpleGraph R.Vertex where
  Adj x y :=
    (fkRectTorusGraph R).Adj x y ∧
      fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta) s(x, y) = true ∧
      s(x, y) ∉ fkRectPrimalUnexploredEdges R S eta
  symm := by
    constructor
    rintro x y ⟨hxy, hopen, hout⟩
    refine ⟨hxy.symm, ?_, ?_⟩ <;> simpa only [Sym2.eq_swap]
  loopless := ⟨by rintro x ⟨hxx, _, _⟩; exact hxx.ne rfl⟩

end
end StatMech.FrontierD
