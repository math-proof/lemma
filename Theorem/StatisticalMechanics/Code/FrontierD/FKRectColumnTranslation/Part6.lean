/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectColumnTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectOrientedEvenRowBlock.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectColumnTranslation.Part6
open Set SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectOpenEdgeCount_columnTranslation
    (R : FKRectTorus) (s : Int) (omega : R.Configuration) :
    fkRectOpenEdgeCount R
        (fkRectColumnTranslationConfigurationEquiv R s omega) =
      fkRectOpenEdgeCount R omega := by
  unfold fkRectOpenEdgeCount
  let E := fkRectColumnTranslationEdgeEquiv R s
  apply Finset.card_bij (fun a _ => E.symm a)
  · intro a ha
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
  · intro a ha b hb hab
    exact E.symm.injective hab
  · intro b hb
    refine ⟨E b, ?_, E.symm_apply_apply b⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    change omega (E.symm (E b)) = true
    rwa [E.symm_apply_apply]

theorem fkRectNumClusters_columnTranslation
    (R : FKRectTorus) (s : Int) (omega : R.Configuration) :
    fkRectNumClusters R
        (fkRectColumnTranslationConfigurationEquiv R s omega) =
      fkRectNumClusters R omega := by
  unfold fkRectNumClusters
  exact (Fintype.card_congr
    (fkRectOpenGraphColumnTranslationIso
      R s omega).connectedComponentEquiv).symm

theorem fkRectCriticalReducedWeight_columnTranslation
    (R : FKRectTorus) (s : Int) (q : Real) (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q
        (fkRectColumnTranslationConfigurationEquiv R s omega) =
      fkRectCriticalReducedWeight R q omega := by
  unfold fkRectCriticalReducedWeight
  rw [fkRectOpenEdgeCount_columnTranslation,
    fkRectNumClusters_columnTranslation]

theorem fkRectCriticalReducedZ_columnTranslation
    (R : FKRectTorus) (s : Int) (q : Real) :
    (∑ omega : R.Configuration,
        fkRectCriticalReducedWeight R q
          (fkRectColumnTranslationConfigurationEquiv R s omega)) =
      fkRectCriticalReducedZ R q := by
  simp only [fkRectCriticalReducedWeight_columnTranslation]
  rfl

theorem fkRectCriticalRandomClusterProb_columnTranslation
    (R : FKRectTorus) (s : Int) (q : Real) (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q
        (fkRectColumnTranslationConfigurationEquiv R s omega) =
      fkRectCriticalRandomClusterProb R q omega := by
  unfold fkRectCriticalRandomClusterProb
  rw [fkRectCriticalReducedWeight_columnTranslation]


theorem fkRectCriticalEventMass_columnTranslation
    (R : FKRectTorus) (s : Int) (q : Real)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass R q A =
      fkRectCriticalEventMass R q
        ((fkRectColumnTranslationConfigurationEquiv R s) '' A) := by
  classical
  let C := fkRectColumnTranslationConfigurationEquiv R s
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta : R.Configuration =>
    (C '' A).indicator
      (fun eta => fkRectCriticalRandomClusterProb R q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hmem : C omega ∈ C '' A ↔ omega ∈ A := by
    constructor
    · rintro ⟨eta, heta, heq⟩
      exact C.injective heq ▸ heta
    · intro homega
      exact ⟨omega, homega, rfl⟩
  have hprob := fkRectCriticalRandomClusterProb_columnTranslation
    R s q omega
  by_cases hA : omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (hmem.mpr hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (fun h => hA (hmem.mp h))]


end
end StatMech.FrontierD
