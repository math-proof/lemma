/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRandomClusterFiniteEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFKG.Part2
import Theorem.StatisticalMechanics.Code.FK.CircuitLowerBound.Part6
import Theorem.StatisticalMechanics.Code.FK.FinitePatternEnergy.Part3
import Instance.StatisticalMechanics.Code.FrontierD.FKRectRandomClusterFiniteEnergy
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech

@[simp] theorem fkRectGraphConfigurationExtend_setOpen
    (R : FKRectTorus) (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) :
    fkRectGraphConfigurationExtend R (setOpen e eta) =
      setOpen e.1 (fkRectGraphConfigurationExtend R eta) := by
  funext x
  by_cases hx : x = e.1
  · subst x
    simp [fkRectGraphConfigurationExtend, e.2]
  · by_cases hxe : x ∈ (fkRectTorusGraph R).edgeSet
    · have hsub : (⟨x, hxe⟩ : {x // x ∈ (fkRectTorusGraph R).edgeSet}) ≠ e :=
        fun h => hx (congrArg Subtype.val h)
      simp [fkRectGraphConfigurationExtend, hxe,
        setOpen_of_ne hsub, setOpen_of_ne hx]
    · simp [fkRectGraphConfigurationExtend, hxe,
        setOpen_of_ne hx]

@[simp] theorem fkRectGraphConfigurationExtend_setClosed
    (R : FKRectTorus) (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) :
    fkRectGraphConfigurationExtend R (setClosed e eta) =
      setClosed e.1 (fkRectGraphConfigurationExtend R eta) := by
  funext x
  by_cases hx : x = e.1
  · subst x
    simp [fkRectGraphConfigurationExtend, e.2]
  · by_cases hxe : x ∈ (fkRectTorusGraph R).edgeSet
    · have hsub : (⟨x, hxe⟩ : {x // x ∈ (fkRectTorusGraph R).edgeSet}) ≠ e :=
        fun h => hx (congrArg Subtype.val h)
      simp [fkRectGraphConfigurationExtend, hxe,
        setClosed_of_ne hsub, setClosed_of_ne hx]
    · simp [fkRectGraphConfigurationExtend, hxe,
        setClosed_of_ne hx]


theorem fkRectGraphCriticalProb_setClosed_ge
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) :
    FK.cFE (fkRectCriticalP q) q *
        (fkRectGraphCriticalRandomClusterProb R q
            (setOpen e eta) +
          fkRectGraphCriticalRandomClusterProb R q
            (setClosed e eta)) ≤
      fkRectGraphCriticalRandomClusterProb R q
        (setClosed e eta) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp : 0 < fkRectCriticalP q := fkRectCriticalP_pos hq0
  have hp1 : fkRectCriticalP q < 1 := fkRectCriticalP_lt_one hq0
  have hraw := FK.fkWeight_setClosed_ge (fkRectTorusGraph R)
    hp hp1 hq e.1 (fkRectGraphConfigurationExtend R eta)
  rw [← fkRectGraphConfigurationExtend_setOpen,
    ← fkRectGraphConfigurationExtend_setClosed] at hraw
  simp_rw [fkWeight_configurationExtend_critical R hq0] at hraw
  have hfactor : 0 < fkRectCriticalEdgeFactor R q :=
    fkRectCriticalEdgeFactor_pos R hq0
  have hreduced :
      FK.cFE (fkRectCriticalP q) q *
          (fkRectGraphCriticalReducedWeight R q
              (setOpen e eta) +
            fkRectGraphCriticalReducedWeight R q
              (setClosed e eta)) ≤
        fkRectGraphCriticalReducedWeight R q
          (setClosed e eta) := by
    nlinarith
  have hZ : 0 < fkRectGraphCriticalReducedZ R q :=
    fkRectGraphCriticalReducedZ_pos R hq0
  unfold fkRectGraphCriticalRandomClusterProb
  rw [← add_div]
  rw [show FK.cFE (fkRectCriticalP q) q *
      ((fkRectGraphCriticalReducedWeight R q
            (setOpen e eta) +
          fkRectGraphCriticalReducedWeight R q
            (setClosed e eta)) /
        fkRectGraphCriticalReducedZ R q) =
      (FK.cFE (fkRectCriticalP q) q *
        (fkRectGraphCriticalReducedWeight R q
            (setOpen e eta) +
          fkRectGraphCriticalReducedWeight R q
            (setClosed e eta))) /
        fkRectGraphCriticalReducedZ R q by ring]
  exact (div_le_div_iff_of_pos_right hZ).2 hreduced


theorem fkRectGraphCriticalProb_setOpen_ge
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (e : {e // e ∈ (fkRectTorusGraph R).edgeSet})
    (eta : FKRectGraphConfiguration R) :
    FK.cFE (fkRectCriticalP q) q *
        (fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) +
          fkRectGraphCriticalRandomClusterProb R q (setClosed e eta)) ≤
      fkRectGraphCriticalRandomClusterProb R q (setOpen e eta) := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hp : 0 < fkRectCriticalP q := fkRectCriticalP_pos hq0
  have hp1 : fkRectCriticalP q < 1 := fkRectCriticalP_lt_one hq0
  have hraw := FK.fkWeight_setOpen_ge (fkRectTorusGraph R)
    hp hp1 hq e.1 (fkRectGraphConfigurationExtend R eta)
  rw [← fkRectGraphConfigurationExtend_setOpen,
    ← fkRectGraphConfigurationExtend_setClosed] at hraw
  simp_rw [fkWeight_configurationExtend_critical R hq0] at hraw
  have hfactor : 0 < fkRectCriticalEdgeFactor R q :=
    fkRectCriticalEdgeFactor_pos R hq0
  have hreduced :
      FK.cFE (fkRectCriticalP q) q *
          (fkRectGraphCriticalReducedWeight R q (setOpen e eta) +
            fkRectGraphCriticalReducedWeight R q (setClosed e eta)) ≤
        fkRectGraphCriticalReducedWeight R q (setOpen e eta) := by
    nlinarith
  have hZ : 0 < fkRectGraphCriticalReducedZ R q :=
    fkRectGraphCriticalReducedZ_pos R hq0
  unfold fkRectGraphCriticalRandomClusterProb
  rw [← add_div]
  rw [show FK.cFE (fkRectCriticalP q) q *
      ((fkRectGraphCriticalReducedWeight R q (setOpen e eta) +
          fkRectGraphCriticalReducedWeight R q (setClosed e eta)) /
        fkRectGraphCriticalReducedZ R q) =
      (FK.cFE (fkRectCriticalP q) q *
        (fkRectGraphCriticalReducedWeight R q (setOpen e eta) +
          fkRectGraphCriticalReducedWeight R q (setClosed e eta))) /
        fkRectGraphCriticalReducedZ R q by ring]
  exact (div_le_div_iff_of_pos_right hZ).2 hreduced


end
end StatMech.FrontierD
