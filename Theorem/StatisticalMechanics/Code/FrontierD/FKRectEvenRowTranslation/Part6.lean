/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectEvenRowTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedAxisSource
import Def.StatisticalMechanics.Code.FrontierD.FKRectEvenRowTranslation.Part6
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectOpenEdgeCount_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (omega : R.Configuration) :
    fkRectOpenEdgeCount R
        (fkRectEvenRowTranslationConfigurationEquiv R s omega) =
      fkRectOpenEdgeCount R omega := by
  unfold fkRectOpenEdgeCount
  let E := fkRectEvenRowTranslationEdgeEquiv R s
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

theorem fkRectNumClusters_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s)
    (omega : R.Configuration) :
    fkRectNumClusters R
        (fkRectEvenRowTranslationConfigurationEquiv R s omega) =
      fkRectNumClusters R omega := by
  unfold fkRectNumClusters
  exact (Fintype.card_congr
    (fkRectOpenGraphEvenRowTranslationIso
      R s hs omega).connectedComponentEquiv).symm

theorem fkRectCriticalReducedWeight_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight R q
        (fkRectEvenRowTranslationConfigurationEquiv R s omega) =
      fkRectCriticalReducedWeight R q omega := by
  unfold fkRectCriticalReducedWeight
  rw [fkRectOpenEdgeCount_evenRowTranslation,
    fkRectNumClusters_evenRowTranslation R s hs]

theorem fkRectCriticalRandomClusterProb_evenRowTranslation
    (R : FKRectTorus) (s : Nat) (hs : Even s) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb R q
        (fkRectEvenRowTranslationConfigurationEquiv R s omega) =
      fkRectCriticalRandomClusterProb R q omega := by
  unfold fkRectCriticalRandomClusterProb
  rw [fkRectCriticalReducedWeight_evenRowTranslation R s hs]


end
end StatMech.FrontierD
