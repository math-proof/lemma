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
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part7
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem fkRectPrimalFullDistinctCrossingWitness_congr_openSub
    (R : FKRectTorus) (S : Finset (Fin R.height))
    {rho sigma : ConfigSpace (Sym2 R.Vertex)}
    (hgraph : FK.openSub (fkRectCutGraph R) rho =
      FK.openSub (fkRectCutGraph R) sigma) :
    FKRectPrimalFullDistinctCrossingWitness R S rho ↔
      FKRectPrimalFullDistinctCrossingWitness R S sigma := by
  unfold FKRectPrimalFullDistinctCrossingWitness
    FKRectPrimalFullCrossingSource
  rw [hgraph]

theorem fkRectPrimalStableCrossingWitness_cutConfigOfFull_iff
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (rho : ConfigSpace (Sym2 R.Vertex)) :
    FKRectPrimalStableCrossingWitnessCore R S
        (fkRectCutConfigOfFull R rho).1 ↔
      FKRectPrimalFullDistinctCrossingWitness R S rho := by
  unfold FKRectPrimalStableCrossingWitnessCore
  have hforce : fkRectForceCutClosed R (fkRectCutConfigOfFull R rho).1 =
      (fkRectCutConfigOfFull R rho).1 := (fkRectCutConfigOfFull R rho).2
  rw [hforce]
  apply fkRectPrimalFullDistinctCrossingWitness_congr_openSub
  calc
    FK.openSub (fkRectCutGraph R)
        (fkRectFullGraphConfiguration R (fkRectCutConfigOfFull R rho).1) =
      fkRectOpenGraph R (fkRectCutConfigOfFull R rho).1 :=
        fkRectCut_openSub_eq R (fkRectCutConfigOfFull R rho)
    _ = FK.openSub (fkRectCutGraph R) rho :=
      fkRectOpenGraph_cutConfigOfFull R rho


theorem fkRectCutGraph_stableWitnessEvent_eq
    (R : FKRectTorus) (S : Finset (Fin R.height)) :
    FK.ecz_closeOff (fkRectCutGraph R) ⁻¹'
        fkRectCutEdgeEvent R
          {eta | FKRectPrimalStableCrossingWitnessCore R S eta} =
      {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := by
  ext rho
  change FKRectPrimalStableCrossingWitnessCore R S
      ((fkRectCutClosedEdgeConfigEquiv R).symm
        (FK.ecz_closeOff (fkRectCutGraph R) rho)).1 ↔ _
  exact fkRectPrimalStableCrossingWitness_cutConfigOfFull_iff R S rho


theorem fkRectCriticalCutFree_stableWitness_eq_finiteEventMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (S : Finset (Fin R.height)) :
    fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalStableCrossingWitnessCore R S eta} =
      StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) (fkRectCriticalP q) q)
        {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := by
  rw [fkRectCriticalCutFreeEventMass_eq_cutGraph R hq,
    fkRectCutGraph_stableWitnessEvent_eq]
  unfold StatMech.Probability.finiteEventMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hmem : FKRectPrimalFullDistinctCrossingWitness R S rho
  · have hs : rho ∈
        {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := hmem
    simp [Set.indicator, hs]
  · have hs : rho ∉
        {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} := hmem
    simp [Set.indicator, hs]


theorem fkRectCriticalCutFree_stableWitness_step
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (S : Finset (Fin R.height)) (i : Fin R.height) (hi : i ∉ S) :
    fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalStableCrossingWitnessCore R (insert i S) eta} ≤
      (FK.freeInfiniteVolume 2
        (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
        (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
        (zero_lt_one.trans_le hq) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2)) *
        fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalStableCrossingWitnessCore R S eta} := by
  rw [fkRectCriticalCutFree_stableWitness_eq_finiteEventMass R hq,
    fkRectCriticalCutFree_stableWitness_eq_finiteEventMass R hq]
  exact fkRectPrimalFullDistinctCrossingWitness_step R S i hi
    (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
    (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq


theorem fkRectPrimalFullDistinctCrossingWitness_mass_le_pow
    (R : FKRectTorus) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    (S : Finset (Fin R.height)) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} ≤
      ((FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace
          (Sym2 (StatMech.Lattice.Site 2)))).real
        (FK.boxBdryConnEvent 2 (R.width - 2))) ^ S.card := by
  classical
  let a := (FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
    MeasureTheory.Measure (ConfigSpace
      (Sym2 (StatMech.Lattice.Site 2)))).real
    (FK.boxBdryConnEvent 2 (R.width - 2))
  have ha : 0 ≤ a := MeasureTheory.measureReal_nonneg
  change StatMech.Probability.finiteEventMass
      (FK.fkProb (fkRectCutGraph R) p q)
      {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} ≤ a ^ S.card
  induction S using Finset.induction_on with
  | empty =>
      calc
        StatMech.Probability.finiteEventMass
            (FK.fkProb (fkRectCutGraph R) p q)
            {rho | FKRectPrimalFullDistinctCrossingWitness R ∅ rho} = 1 := by
              unfold StatMech.Probability.finiteEventMass
              have hevent : {rho : ConfigSpace (Sym2 R.Vertex) |
                  FKRectPrimalFullDistinctCrossingWitness R ∅ rho} = Set.univ := by
                ext rho
                simp [FKRectPrimalFullDistinctCrossingWitness]
              rw [hevent]
              simpa using FK.fkProb_sum_eq_one (fkRectCutGraph R)
                hp hp1 (zero_lt_one.trans_le hq)
        _ ≤ a ^ (∅ : Finset (Fin R.height)).card := by
          rw [Finset.card_empty, pow_zero]
  | @insert i S hi ih =>
      calc
        StatMech.Probability.finiteEventMass
            (FK.fkProb (fkRectCutGraph R) p q)
            {rho | FKRectPrimalFullDistinctCrossingWitness R (insert i S) rho} ≤
          a * StatMech.Probability.finiteEventMass
            (FK.fkProb (fkRectCutGraph R) p q)
            {rho | FKRectPrimalFullDistinctCrossingWitness R S rho} :=
              fkRectPrimalFullDistinctCrossingWitness_step
                R S i hi hp hp1 hq
        _ ≤ a * a ^ S.card := mul_le_mul_of_nonneg_left ih ha
        _ = a ^ (insert i S).card := by
          rw [Finset.card_insert_of_notMem hi, pow_succ]
          ring


end
end StatMech.FrontierD
