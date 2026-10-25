/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectPrimalAdaptivePairedConnection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectPrimalPairedConnection
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptivePairedConnection.Part4
open MeasureTheory SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectPrimalFullDistinctPairedWitness_congr_openSub
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height))
    {rho sigma : ConfigSpace (Sym2 R.Vertex)}
    (hgraph : FK.openSub (fkRectCutGraph R) rho =
      FK.openSub (fkRectCutGraph R) sigma) :
    FKRectPrimalFullDistinctPairedWitness R pair S rho <->
      FKRectPrimalFullDistinctPairedWitness R pair S sigma := by
  unfold FKRectPrimalFullDistinctPairedWitness
  rw [hgraph]

theorem fkRectPrimalStablePairedWitness_cutConfigOfFull_iff
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) (rho : ConfigSpace (Sym2 R.Vertex)) :
    FKRectPrimalStablePairedWitnessCore R pair S
        (fkRectCutConfigOfFull R rho).1 <->
      FKRectPrimalFullDistinctPairedWitness R pair S rho := by
  unfold FKRectPrimalStablePairedWitnessCore
  have hforce : fkRectForceCutClosed R (fkRectCutConfigOfFull R rho).1 =
      (fkRectCutConfigOfFull R rho).1 := (fkRectCutConfigOfFull R rho).2
  rw [hforce]
  apply fkRectPrimalFullDistinctPairedWitness_congr_openSub
  calc
    FK.openSub (fkRectCutGraph R)
        (fkRectFullGraphConfiguration R (fkRectCutConfigOfFull R rho).1) =
      fkRectOpenGraph R (fkRectCutConfigOfFull R rho).1 :=
        fkRectCut_openSub_eq R (fkRectCutConfigOfFull R rho)
    _ = FK.openSub (fkRectCutGraph R) rho :=
      fkRectOpenGraph_cutConfigOfFull R rho

theorem fkRectCutGraph_stablePairedWitnessEvent_eq
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    (S : Finset (Fin R.height)) :
    FK.ecz_closeOff (fkRectCutGraph R) ⁻¹'
        fkRectCutEdgeEvent R
          {eta | FKRectPrimalStablePairedWitnessCore R pair S eta} =
      {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} := by
  ext rho
  change FKRectPrimalStablePairedWitnessCore R pair S
      ((fkRectCutClosedEdgeConfigEquiv R).symm
        (FK.ecz_closeOff (fkRectCutGraph R) rho)).1 <-> _
  exact fkRectPrimalStablePairedWitness_cutConfigOfFull_iff R pair S rho


theorem fkRectCriticalCutFree_stablePairedWitness_eq_finiteEventMass
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {q : Real} (hq : 1 <= q) (S : Finset (Fin R.height)) :
    fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalStablePairedWitnessCore R pair S eta} =
      StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) (fkRectCriticalP q) q)
        {rho | FKRectPrimalFullDistinctPairedWitness R pair S rho} := by
  rw [fkRectCriticalCutFreeEventMass_eq_cutGraph R hq,
    fkRectCutGraph_stablePairedWitnessEvent_eq R pair S]
  unfold StatMech.Probability.finiteEventMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hmem : FKRectPrimalFullDistinctPairedWitness R pair S rho
  · simp [Set.indicator, hmem]
  · simp [Set.indicator, hmem]


theorem fkRectCriticalCutFree_stablePairedWitness_le_prod
    (R : FKRectTorus) (pair : Fin R.height -> Fin R.height)
    {q : Real} (hq : 1 <= q) (S : Finset (Fin R.height)) :
    fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalStablePairedWitnessCore R pair S eta} <=
      ∏ i ∈ S,
        fkRectPrimalPairedConnectionFactor R pair
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq i := by
  rw [fkRectCriticalCutFree_stablePairedWitness_eq_finiteEventMass
    R pair hq S]
  exact fkRectPrimalFullDistinctPairedWitness_mass_le_prod R pair
    (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
    (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq S

end
end StatMech.FrontierD
