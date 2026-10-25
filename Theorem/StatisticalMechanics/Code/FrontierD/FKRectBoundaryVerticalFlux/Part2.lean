/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part11
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryVerticalFlux
open Equiv Finset SimpleGraph
open StatMech.Onsager StatMech.Onsager.BaseCase


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem fkMedialVerticalSeamBlackDart_fst
    (pairing : FKMedialLoopPairing T) (i : Fin T.width) :
    (fkMedialVerticalSeamBlackDart pairing i).1.1.1 = i := by
  unfold fkMedialVerticalSeamBlackDart
  dsimp only
  split
  · cases h : pairing (i, (⟨0, T.height_pos⟩ : Fin T.height)) <;>
      simp [fkMedialVerticalSeamDart, fkMedialBondMate,
        fkMedialLocalMate, finitePeriodicSucc_svFinLast, h]
  · cases h : pairing (i, svFinLast T.height_pos) <;>
      simp [fkMedialVerticalSeamDart, fkMedialLocalMate, h]

theorem fkMedialVerticalSeamBlackDart_injective
    (pairing : FKMedialLoopPairing T) :
    Function.Injective (fkMedialVerticalSeamBlackDart pairing) := by
  intro i j hij
  have hv := congrArg (fun d : FKMedialBlackDart T => d.1.1.1) hij
  simpa using hv

theorem fkMedialVerticalSeamBlackDart_component
    (pairing : FKMedialLoopPairing T) (i : Fin T.width) :
    (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialVerticalSeamBlackDart pairing i).1 =
      (fkMedialLoopGraph T pairing).connectedComponentMk
        (fkMedialVerticalSeamDart T i) := by
  unfold fkMedialVerticalSeamBlackDart
  dsimp only
  by_cases hs : fkMedialCheckerColor (fkMedialVerticalSeamDart T i) = false
  · rw [dif_pos hs]
    apply ConnectedComponent.sound
    have hreach := fkMedialBoundaryStep_reachable pairing
      (fkMedialLocalMate pairing
        (fkMedialBondMate T (fkMedialVerticalSeamDart T i)))
    simpa [fkMedialBoundaryStep_apply, fkMedialLocalMate_involutive,
      fkMedialBondMate_involutive] using hreach
  · rw [dif_neg hs]
    apply ConnectedComponent.sound
    exact (fkMedial_reachable_localMate pairing
      (fkMedialVerticalSeamDart T i)).symm


theorem fkMedialLoopCanonicalVerticalFlux_eq_blackCycleContribution
    (pairing : FKMedialLoopPairing T) (d : FKMedialBlackDart T) :
    fkMedialLoopCanonicalVerticalFlux pairing
        ((fkMedialLoopGraph T pairing).connectedComponentMk d.1) =
      ∑ e : FKMedialBlackDart T,
        if (fkMedialBlackBoundaryPerm pairing).SameCycle d e then
          fkMedialBlackVerticalSeamContribution pairing e
        else 0 := by
  classical
  unfold fkMedialLoopCanonicalVerticalFlux
    fkMedialBlackVerticalSeamContribution
  calc
    (∑ i : Fin T.width,
        if (fkMedialLoopGraph T pairing).connectedComponentMk
              (fkMedialVerticalSeamDart T i) =
            (fkMedialLoopGraph T pairing).connectedComponentMk d.1 then
          fkMedialCanonicalVerticalSeamSign T i else 0) =
      ∑ i : Fin T.width, ∑ e : FKMedialBlackDart T,
        if (fkMedialBlackBoundaryPerm pairing).SameCycle d e then
          (if fkMedialVerticalSeamBlackDart pairing i = e then
            fkMedialCanonicalVerticalSeamSign T i else 0)
        else 0 := by
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hcomponent :
          (fkMedialLoopGraph T pairing).connectedComponentMk
              (fkMedialVerticalSeamDart T i) =
            (fkMedialLoopGraph T pairing).connectedComponentMk d.1
      · rw [if_pos hcomponent]
        have hreach : (fkMedialLoopGraph T pairing).Reachable d.1
            (fkMedialVerticalSeamBlackDart pairing i).1 := by
          apply ConnectedComponent.exact
          rw [fkMedialVerticalSeamBlackDart_component]
          exact hcomponent.symm
        have hcycle : (fkMedialBlackBoundaryPerm pairing).SameCycle d
            (fkMedialVerticalSeamBlackDart pairing i) :=
          (fkMedial_blackBoundary_sameCycle_iff_reachable pairing _ _).2 hreach
        rw [Finset.sum_eq_single
          (fkMedialVerticalSeamBlackDart pairing i)]
        · simp [hcycle]
        · intro e he hne
          simp [hne.symm]
        · simp
      · rw [if_neg hcomponent]
        symm
        apply Finset.sum_eq_zero
        intro e he
        by_cases hie : fkMedialVerticalSeamBlackDart pairing i = e
        · subst e
          have hcycle : ¬ (fkMedialBlackBoundaryPerm pairing).SameCycle d
              (fkMedialVerticalSeamBlackDart pairing i) := by
            intro h
            apply hcomponent
            have hreach :=
              (fkMedial_blackBoundary_sameCycle_iff_reachable pairing _ _).1 h
            have hc := ConnectedComponent.sound hreach
            rw [fkMedialVerticalSeamBlackDart_component] at hc
            exact hc.symm
          simp [hcycle]
        · simp [hie]
    _ = ∑ e : FKMedialBlackDart T,
        if (fkMedialBlackBoundaryPerm pairing).SameCycle d e then
          ∑ i : Fin T.width,
            if fkMedialVerticalSeamBlackDart pairing i = e then
              fkMedialCanonicalVerticalSeamSign T i else 0
        else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      by_cases hcycle : (fkMedialBlackBoundaryPerm pairing).SameCycle d e
      · simp [hcycle]
      · simp [hcycle]


end
end StatMech.FrontierD
