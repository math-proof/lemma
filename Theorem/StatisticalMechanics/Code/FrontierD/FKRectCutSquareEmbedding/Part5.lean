/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutSquareEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCrossingExploration.Part8
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusSquareDevelopment.Part12
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQConsumer.Part5
import Theorem.StatisticalMechanics.Code.FK.FKGeneralQTranslation.Part2
import Theorem.StatisticalMechanics.Code.FK.TwoPointPositiveFull
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part4
open MeasureTheory StatMech.Lattice SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPrimalUnexploredBoxEmbedding_injective
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    Function.Injective
      (fkRectPrimalUnexploredBoxEmbedding R S eta) := by
  intro x y hxy
  apply Subtype.ext
  exact fkRectVertexBoxEmbedding_injective R hxy

theorem fkRectPrimalUnexplored_boxAdjMatch
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    FK.ocd_AdjMatch
      (fkRectPrimalUnexploredInducedGraph R S eta)
      (FK.boxGraph 2 (R.width + R.height))
      (fkRectPrimalUnexploredBoxEmbedding R S eta) := by
  intro x y
  change (fkRectCutGraph R).Adj x.1 y.1 ↔ _
  exact fkRectCutGraph_boxAdjMatch R x.1 y.1


theorem fkRectPrimalUnexplored_freeEvent_le_box
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace
      (Sym2 (FKRectPrimalUnexploredVertex R S eta)))}
    (hA : IsIncreasing A) :
    (∑ omega,
        A.indicator (fun _ => (1 : Real)) omega *
          FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta)
            p q omega) ≤
      ∑ rho,
        (FK.ocd_innerRestrict
          (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹' A).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (FK.boxGraph 2 (R.width + R.height)) p q rho := by
  exact FK.ocd_free_inner_le_outer_fkProb
    (fkRectPrimalUnexploredInducedGraph R S eta)
    (FK.boxGraph 2 (R.width + R.height))
    (fkRectPrimalUnexploredBoxEmbedding R S eta)
    (fkRectPrimalUnexploredBoxEmbedding_injective R S eta)
    (fkRectPrimalUnexplored_boxAdjMatch R S eta)
    hp hp1 hq hA


theorem fkRectPrimalUnexplored_freeEvent_le_freeInfinite
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace
      (Sym2 (FKRectPrimalUnexploredVertex R S eta)))}
    (hA : IsIncreasing A) :
    (∑ omega,
        A.indicator (fun _ => (1 : Real)) omega *
          FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta)
            p q omega) ≤
      (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (FK.boxRestrict 2 (R.width + R.height) ⁻¹'
          (FK.ocd_innerRestrict
            (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹' A)) := by
  have hpre : IsIncreasing
      (FK.ocd_innerRestrict
        (fkRectPrimalUnexploredBoxEmbedding R S eta) ⁻¹' A) := by
    intro rho rho' hrho hmem
    apply hA _ hmem
    intro e
    exact hrho _
  exact (fkRectPrimalUnexplored_freeEvent_le_box
    R S eta hp hp1 hq hA).trans
      (freeBoxEvent_le_freeInfinite
        (R.width + R.height) hp hp1 hq hpre)


end
end StatMech.FrontierD
