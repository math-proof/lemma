/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectQuarterTurn.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectDevelopedSquareReflection.Part6
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusCrossingEvents.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectQuarterTurn.Part8
open Set SimpleGraph StatMech.Lattice


namespace StatMech.FrontierD

noncomputable section

theorem fkRectOpenEdgeCount_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration) :
    fkRectOpenEdgeCount (fkRectQuarterTurnTorus R hheight)
        (fkRectQuarterTurnConfigurationEquiv R hheight omega) =
      fkRectOpenEdgeCount R omega := by
  unfold fkRectOpenEdgeCount
  let E := fkRectQuarterTurnEdgeEquiv R hheight
  apply Finset.card_bij (fun a _ => E.symm a)
  · intro a ha
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ha
  · intro a ha b hb hab
    exact E.symm.injective hab
  · intro b hb
    refine ⟨E b, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      change omega (E.symm (E b)) = true
      rwa [E.symm_apply_apply]
    · exact E.symm_apply_apply b


theorem fkRectNumClusters_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height)
    (omega : R.Configuration) :
    fkRectNumClusters (fkRectQuarterTurnTorus R hheight)
        (fkRectQuarterTurnConfigurationEquiv R hheight omega) =
      fkRectNumClusters R omega := by
  unfold fkRectNumClusters
  exact (Fintype.card_congr
    (fkRectOpenGraphQuarterTurnIso R hheight omega).connectedComponentEquiv).symm


theorem fkRectCriticalReducedWeight_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalReducedWeight (fkRectQuarterTurnTorus R hheight) q
        (fkRectQuarterTurnConfigurationEquiv R hheight omega) =
      fkRectCriticalReducedWeight R q omega := by
  unfold fkRectCriticalReducedWeight
  rw [fkRectOpenEdgeCount_quarterTurn, fkRectNumClusters_quarterTurn]


theorem fkRectCriticalReducedZ_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (q : Real) :
    fkRectCriticalReducedZ (fkRectQuarterTurnTorus R hheight) q =
      fkRectCriticalReducedZ R q := by
  unfold fkRectCriticalReducedZ
  rw [← Equiv.sum_comp (fkRectQuarterTurnConfigurationEquiv R hheight)
    (fkRectCriticalReducedWeight (fkRectQuarterTurnTorus R hheight) q)]
  apply Finset.sum_congr rfl
  intro omega homega
  exact fkRectCriticalReducedWeight_quarterTurn R hheight q omega


theorem fkRectCriticalRandomClusterProb_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (q : Real)
    (omega : R.Configuration) :
    fkRectCriticalRandomClusterProb (fkRectQuarterTurnTorus R hheight) q
        (fkRectQuarterTurnConfigurationEquiv R hheight omega) =
      fkRectCriticalRandomClusterProb R q omega := by
  unfold fkRectCriticalRandomClusterProb
  rw [fkRectCriticalReducedWeight_quarterTurn,
    fkRectCriticalReducedZ_quarterTurn]


theorem fkRectCriticalEventMass_quarterTurn
    (R : FKRectTorus) (hheight : 4 < R.height) (q : Real)
    (A : Set (fkRectQuarterTurnTorus R hheight).Configuration) :
    fkRectCriticalEventMass (fkRectQuarterTurnTorus R hheight) q A =
      fkRectCriticalEventMass R q
        ((fkRectQuarterTurnConfigurationEquiv R hheight) ⁻¹' A) := by
  classical
  let C := fkRectQuarterTurnConfigurationEquiv R hheight
  unfold fkRectCriticalEventMass
  rw [← Equiv.sum_comp C (fun eta =>
    A.indicator (fun eta => fkRectCriticalRandomClusterProb
      (fkRectQuarterTurnTorus R hheight) q eta) eta)]
  apply Finset.sum_congr rfl
  intro omega _
  have hprob : fkRectCriticalRandomClusterProb
      (fkRectQuarterTurnTorus R hheight) q (C omega) =
        fkRectCriticalRandomClusterProb R q omega :=
    fkRectCriticalRandomClusterProb_quarterTurn R hheight q omega
  by_cases hA : C omega ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (show omega ∈ C ⁻¹' A from hA), hprob]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem
        (show omega ∉ C ⁻¹' A from hA)]


theorem fkRectCriticalEventMass_quarterTurn_image
    (R : FKRectTorus) (hheight : 4 < R.height) (q : Real)
    (A : Set R.Configuration) :
    fkRectCriticalEventMass (fkRectQuarterTurnTorus R hheight) q
        (fkRectQuarterTurnConfigurationEquiv R hheight '' A) =
      fkRectCriticalEventMass R q A := by
  rw [fkRectCriticalEventMass_quarterTurn]
  congr 1
  ext omega
  simp


end
end StatMech.FrontierD
