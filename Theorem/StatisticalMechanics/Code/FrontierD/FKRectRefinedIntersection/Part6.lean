/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRefinedIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedInteractionCore.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part5
open scoped BigOperators
open Finset


namespace StatMech.FrontierD

open StatMech.Onsager

open IntegralSquareTorusCycle

noncomputable section

variable {L : Nat} [Fact (8 < L)]

theorem fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (t : Int × Int) (n : Nat) :
    fkRectRefinedBoundaryCenterAfter pairing d
        ((fkRectRefinedBoundaryCanonicalCenter R d).1 + t.1,
          (fkRectRefinedBoundaryCanonicalCenter R d).2 + t.2) n =
      ((fkRectRefinedBoundaryCanonicalCenter R
          ((fkMedialBoundaryStep pairing)^[n] d)).1 + t.1 +
          4 * (fkRectSquareDeckTranslation R
            (fkRectMedialBoundaryPrimalSeamTrace R pairing d n)).1 +
          (fkRectRefinedBoundaryPrimalPotential R d).1 -
          (fkRectRefinedBoundaryPrimalPotential R
            ((fkMedialBoundaryStep pairing)^[n] d)).1,
        (fkRectRefinedBoundaryCanonicalCenter R
          ((fkMedialBoundaryStep pairing)^[n] d)).2 + t.2 +
          4 * (fkRectSquareDeckTranslation R
            (fkRectMedialBoundaryPrimalSeamTrace R pairing d n)).2 +
          (fkRectRefinedBoundaryPrimalPotential R d).2 -
          (fkRectRefinedBoundaryPrimalPotential R
            ((fkMedialBoundaryStep pairing)^[n] d)).2) := by
  induction n generalizing d t with
  | zero =>
      simp [fkRectRefinedBoundaryCenterAfter,
        fkRectMedialBoundaryPrimalSeamTrace,
        fkRectSquareDeckTranslation]
  | succ n ih =>
      let next := fkMedialBoundaryStep pairing d
      let a := fkRectMedialBoundaryPrimalSeamIncrement R pairing d
      let A := fkRectSquareDeckTranslation R a
      have hone :=
        fkRectRefinedBoundaryBondCenter_eq_canonical_add_deck R pairing d
      have hstart : fkRectRefinedBondCenter
          ((fkRectRefinedBoundaryCanonicalCenter R d).1 + t.1,
            (fkRectRefinedBoundaryCanonicalCenter R d).2 + t.2)
          (fkMedialLocalMate pairing d).2 =
        ((fkRectRefinedBoundaryCanonicalCenter R next).1 +
            (t.1 + 4 * A.1 +
              (fkRectRefinedBoundaryPrimalPotential R d).1 -
              (fkRectRefinedBoundaryPrimalPotential R next).1),
          (fkRectRefinedBoundaryCanonicalCenter R next).2 +
            (t.2 + 4 * A.2 +
              (fkRectRefinedBoundaryPrimalPotential R d).2 -
              (fkRectRefinedBoundaryPrimalPotential R next).2)) := by
        dsimp [next, A, a] at hone ⊢
        have hone1 := congrArg Prod.fst hone
        have hone2 := congrArg Prod.snd hone
        unfold fkRectRefinedBondCenter at hone1 hone2 ⊢
        apply Prod.ext
        · simp only [Prod.fst, Prod.snd] at hone1 ⊢
          omega
        · simp only [Prod.fst, Prod.snd] at hone2 ⊢
          omega
      rw [fkRectRefinedBoundaryCenterAfter, hstart]
      rw [ih next
        (t.1 + 4 * A.1 +
            (fkRectRefinedBoundaryPrimalPotential R d).1 -
            (fkRectRefinedBoundaryPrimalPotential R next).1,
          t.2 + 4 * A.2 +
            (fkRectRefinedBoundaryPrimalPotential R d).2 -
            (fkRectRefinedBoundaryPrimalPotential R next).2)]
      simp only [Function.iterate_succ_apply]
      change _ =
        ((fkRectRefinedBoundaryCanonicalCenter R
              ((fkMedialBoundaryStep pairing)^[n] next)).1 + t.1 +
            4 * (fkRectSquareDeckTranslation R
              (fkRectMedialBoundaryPrimalSeamTrace R pairing d
                (n + 1))).1 +
            (fkRectRefinedBoundaryPrimalPotential R d).1 -
            (fkRectRefinedBoundaryPrimalPotential R
              ((fkMedialBoundaryStep pairing)^[n] next)).1,
          (fkRectRefinedBoundaryCanonicalCenter R
              ((fkMedialBoundaryStep pairing)^[n] next)).2 + t.2 +
            4 * (fkRectSquareDeckTranslation R
              (fkRectMedialBoundaryPrimalSeamTrace R pairing d
                (n + 1))).2 +
            (fkRectRefinedBoundaryPrimalPotential R d).2 -
            (fkRectRefinedBoundaryPrimalPotential R
              ((fkMedialBoundaryStep pairing)^[n] next)).2)
      simp only [fkRectMedialBoundaryPrimalSeamTrace]
      dsimp [next, A, a]
      unfold fkRectSquareDeckTranslation
      apply Prod.ext <;> simp <;> ring


theorem fkRectMedialBoundaryPrimalStepWalk_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalStepWalk R omega d) =
      fkRectMedialBoundaryPrimalSeamIncrement R
        (fkRectConfigurationToMedialPairing R omega) d := by
  by_cases heq : fkRectMedialDartPrimalLabel R d =
      fkRectMedialDartPrimalLabel R
        (fkMedialBoundaryStep
          (fkRectConfigurationToMedialPairing R omega) d)
  · have hseam : fkRectMedialBoundaryPrimalSeamIncrement R
        (fkRectConfigurationToMedialPairing R omega) d = (0, 0) := by
      unfold fkRectMedialBoundaryPrimalSeamIncrement
      rw [← heq]
      dsimp
      rw [fkRectHorizontalSeamIncrement_same_fst,
        fkRectVerticalSeamIncrement_same_snd]
    rw [hseam]
    unfold fkRectMedialBoundaryPrimalStepWalk
    split
    · rw [fkRectWalkWinding_copy]
      rfl
    · contradiction
  · have heq' : ¬ fkRectMedialDartPrimalLabel R d =
        fkRectMedialDartPrimalLabel R
          (fkMedialBondMate R.medialTorus
            (fkMedialLocalMate
              (fkRectConfigurationToMedialPairing R omega) d)) := by
      simpa only [fkMedialBoundaryStep_apply] using heq
    simp [fkRectMedialBoundaryPrimalStepWalk, heq',
      fkRectMedialBoundaryPrimalSeamIncrement, fkRectWalkWinding]


theorem fkRectMedialBoundaryPrimalTrace_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) (n : Nat) :
    fkRectWalkWinding R
        (fkRectMedialBoundaryPrimalTrace R omega d n) =
      fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d n := by
  induction n generalizing d with
  | zero =>
      simp [fkRectMedialBoundaryPrimalTrace, fkRectWalkWinding,
        fkRectMedialBoundaryPrimalSeamTrace]
  | succ n ih =>
      simp only [fkRectMedialBoundaryPrimalTrace]
      change fkRectWalkWinding R
        ((fkRectMedialBoundaryPrimalStepWalk R omega d).append
          (fkRectMedialBoundaryPrimalTrace R omega
            (fkMedialBoundaryStep
              (fkRectConfigurationToMedialPairing R omega) d) n)) = _
      rw [fkRectWalkWinding_append,
        fkRectMedialBoundaryPrimalStepWalk_winding, ih]
      simp [fkRectMedialBoundaryPrimalSeamTrace]


end
end StatMech.FrontierD
