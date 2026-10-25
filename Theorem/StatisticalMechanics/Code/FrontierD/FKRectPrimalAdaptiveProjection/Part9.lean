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
import Def.StatisticalMechanics.Code.FrontierD.FKRectPrimalAdaptiveProjection.Part8
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem fkRectPrimalFullCrossingClusterCount_le_height
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) :
    fkRectPrimalFullCrossingClusterCount R rho ≤ R.height :=
  fkRectRawHorizontalCrossingClusterCount_le_height R _


theorem exists_fkRectPrimalFullDistinctCrossingWitness
    (R : FKRectTorus) (rho : ConfigSpace (Sym2 R.Vertex)) (n : Nat)
    (hn : n ≤ fkRectPrimalFullCrossingClusterCount R rho) :
    ∃ S : Finset (Fin R.height), S.card = n ∧
      FKRectPrimalFullDistinctCrossingWitness R S rho := by
  classical
  let eta := (fkRectCutConfigOfFull R rho).1
  let available := fkRectRawHorizontalCrossingRepresentativeIndices R eta
  have hnAvailable : n ≤ available.card := by
    rw [card_fkRectRawHorizontalCrossingRepresentativeIndices]
    exact hn
  obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq hnAvailable
  refine ⟨S, hcard, ?_, ?_⟩
  · intro i hi
    have hirep := hsub hi
    obtain ⟨z, hiz⟩ :=
      fkRectRawHorizontalCrossingRepresentativeIndices_subset_sources
        R eta i hirep
    refine ⟨z, ?_⟩
    rw [← fkRectOpenGraph_cutConfigOfFull R rho]
    exact hiz
  · intro i hi j hj hij hreach
    have hirep := hsub hi
    have hjrep := hsub hj
    apply hij
    apply eq_of_representativeIndices_of_component_eq R eta hirep hjrep
    apply SimpleGraph.ConnectedComponent.sound
    rw [fkRectOpenGraph_cutConfigOfFull R rho]
    exact hreach


theorem fkRectPrimalFullCrossingTail_le_choose_mul_pow
    (R : FKRectTorus) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) (n : Nat) :
    StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) p q)
        {rho | n < fkRectPrimalFullCrossingClusterCount R rho} ≤
      Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
          MeasureTheory.Measure (ConfigSpace
            (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) := by
  simpa only [Nat.lt_iff_add_one_le] using
    StatMech.Probability.finiteEventMass_tail_le_choose_mul_pow
      (FK.fkProb (fkRectCutGraph R) p q)
      (fun rho => FK.fkProb_nonneg (fkRectCutGraph R)
        hp hp1 (zero_lt_one.trans_le hq) rho)
      (fkRectPrimalFullCrossingClusterCount R) R.height (n + 1)
      ((FK.freeInfiniteVolume 2 hp hp1 (zero_lt_one.trans_le hq) :
        MeasureTheory.Measure (ConfigSpace
          (Sym2 (StatMech.Lattice.Site 2)))).real
        (FK.boxBdryConnEvent 2 (R.width - 2)))
      (FKRectPrimalFullDistinctCrossingWitness R)
      (fun rho htail =>
        exists_fkRectPrimalFullDistinctCrossingWitness R rho (n + 1) htail)
      (fun S hcard => by
        simpa only [hcard] using
          fkRectPrimalFullDistinctCrossingWitness_mass_le_pow
            R hp hp1 hq S)


theorem fkRectCutGraph_primalCrossingTailEvent_eq
    (R : FKRectTorus) (n : Nat) :
    FK.ecz_closeOff (fkRectCutGraph R) ⁻¹'
        fkRectCutEdgeEvent R
          {eta | n < fkRectRawHorizontalCrossingClusterCount R
            (fkRectForceCutClosed R eta)} =
      {rho | n < fkRectPrimalFullCrossingClusterCount R rho} := by
  ext rho
  change n < fkRectRawHorizontalCrossingClusterCount R
      (fkRectForceCutClosed R (fkRectCutConfigOfFull R rho).1) ↔
    n < fkRectPrimalFullCrossingClusterCount R rho
  have hforce : fkRectForceCutClosed R (fkRectCutConfigOfFull R rho).1 =
      (fkRectCutConfigOfFull R rho).1 := (fkRectCutConfigOfFull R rho).2
  rw [hforce]
  rfl


theorem fkRectCriticalCutFree_primalCrossingTail_eq_finiteEventMass
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (n : Nat) :
    fkRectCriticalCutFreeEventMass R q
        {eta | n < fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R eta)} =
      StatMech.Probability.finiteEventMass
        (FK.fkProb (fkRectCutGraph R) (fkRectCriticalP q) q)
        {rho | n < fkRectPrimalFullCrossingClusterCount R rho} := by
  rw [fkRectCriticalCutFreeEventMass_eq_cutGraph R hq,
    fkRectCutGraph_primalCrossingTailEvent_eq]
  unfold StatMech.Probability.finiteEventMass
  apply Finset.sum_congr rfl
  intro rho _
  by_cases hmem : n < fkRectPrimalFullCrossingClusterCount R rho
  · have hs : rho ∈
        {rho | n < fkRectPrimalFullCrossingClusterCount R rho} := hmem
    simp [Set.indicator, hs]
  · have hs : rho ∉
        {rho | n < fkRectPrimalFullCrossingClusterCount R rho} := hmem
    simp [Set.indicator, hs]


theorem fkRectCriticalCutFree_primalCrossingTail_le_choose_mul_pow
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q) (n : Nat) :
    fkRectCriticalCutFreeEventMass R q
        {eta | n < fkRectRawHorizontalCrossingClusterCount R
          (fkRectForceCutClosed R eta)} ≤
      Nat.choose R.height (n + 1) *
        ((FK.freeInfiniteVolume 2
          (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
          (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq))
          (zero_lt_one.trans_le hq) :
            MeasureTheory.Measure (ConfigSpace
              (Sym2 (StatMech.Lattice.Site 2)))).real
          (FK.boxBdryConnEvent 2 (R.width - 2))) ^ (n + 1) := by
  rw [fkRectCriticalCutFree_primalCrossingTail_eq_finiteEventMass R hq n]
  exact fkRectPrimalFullCrossingTail_le_choose_mul_pow R
    (fkRectCriticalP_pos (lt_of_lt_of_le zero_lt_one hq))
    (fkRectCriticalP_lt_one (lt_of_lt_of_le zero_lt_one hq)) hq n

end
end StatMech.FrontierD
