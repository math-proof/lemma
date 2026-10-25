/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutCollision
import Theorem.StatisticalMechanics.Code.FrontierD.IntegerUnitStepPlateau
import Def.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingLevelPlateau.Part2
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBlackBoundaryUnitCutComponent_crossing
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (j : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat) :
    FKRectHorizontalCutPrimalCrossingComponent R
      (fkRectForceHorizontalCutClosed R omega)
      (fkRectBlackBoundaryUnitCutComponent R omega d hpos j) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let ab := fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j
  let a := ab.1
  let b := ab.2
  let r : Int := j.val + 1
  have hs := fkRectBlackBoundaryUnitPlateauEndpoints_spec
    R omega d hpos j
  change 0 < a ∧ a ≤ b ∧ b < _ ∧
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (a - 1)).2 = r - 1 ∧
    (∀ m, a ≤ m → m ≤ b →
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 = r) ∧
    (∀ m < b + 1,
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 < r + 1) ∧
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (b + 1)).2 = r + 1 at hs
  rcases hs with ⟨hapos, hab, hbN, hprev, hconst, hfirst, hnext⟩
  have hentryPrefix := fkRectMedialBoundaryPrimalSeamTrace_succ
    R pairing d.1 (a - 1)
  have haLevel := hconst a le_rfl hab
  have hentry : (fkRectMedialBoundaryPrimalSeamIncrement R pairing
      ((fkMedialBoundaryStep pairing)^[a - 1] d.1)).2 = 1 := by
    have hsnd := congrArg Prod.snd hentryPrefix
    simp only [Prod.snd_add] at hsnd
    have hidx : a - 1 + 1 = a := by omega
    rw [hidx] at hsnd
    omega
  have hentryRows := fkRectVerticalSeamIncrement_eq_one_endpoints R
    (fkRectMedialDartPrimalLabel R
      ((fkMedialBoundaryStep pairing)^[a - 1] d.1))
    (fkRectMedialDartPrimalLabel R
      (fkMedialBoundaryStep pairing
        ((fkMedialBoundaryStep pairing)^[a - 1] d.1))) hentry
  have haIter : (fkMedialBoundaryStep pairing
      ((fkMedialBoundaryStep pairing)^[a - 1] d.1)) =
      (fkMedialBoundaryStep pairing)^[a] d.1 := by
    rw [show a = (a - 1) + 1 by omega]
    exact (Function.iterate_succ_apply'
      (fkMedialBoundaryStep pairing) (a - 1) d.1).symm
  rw [haIter] at hentryRows
  have hexitPrefix := fkRectMedialBoundaryPrimalSeamTrace_succ
    R pairing d.1 b
  have hbLevel := hconst b hab le_rfl
  have hexit : (fkRectMedialBoundaryPrimalSeamIncrement R pairing
      ((fkMedialBoundaryStep pairing)^[b] d.1)).2 = 1 := by
    have hsnd := congrArg Prod.snd hexitPrefix
    simp only [Prod.snd_add] at hsnd
    omega
  have hexitRows := fkRectVerticalSeamIncrement_eq_one_endpoints R
    (fkRectMedialDartPrimalLabel R
      ((fkMedialBoundaryStep pairing)^[b] d.1))
    (fkRectMedialDartPrimalLabel R
      (fkMedialBoundaryStep pairing
        ((fkMedialBoundaryStep pairing)^[b] d.1))) hexit
  have hreach := fkRectBlackBoundaryPlateau_cutReachable
    R omega d hab (by
      intro m ham hmb
      rw [hconst m ham hmb, haLevel])
  refine ⟨⟨(fkRectMedialDartPrimalLabel R
      ((fkMedialBoundaryStep pairing)^[a] d.1)).1, ?_⟩,
    ⟨(fkRectMedialDartPrimalLabel R
      ((fkMedialBoundaryStep pairing)^[b] d.1)).1, ?_⟩⟩
  · unfold fkRectBlackBoundaryUnitCutComponent
    dsimp only
    apply congrArg (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).connectedComponentMk
    exact Prod.ext rfl hentryRows.2.symm
  · unfold fkRectBlackBoundaryUnitCutComponent
    dsimp only
    have hbvertex :
        ((fkRectMedialDartPrimalLabel R
          ((fkMedialBoundaryStep pairing)^[b] d.1)).1,
            fkRectTopRow R) =
          fkRectMedialDartPrimalLabel R
            ((fkMedialBoundaryStep pairing)^[b] d.1) :=
      Prod.ext rfl hexitRows.1.symm
    rw [hbvertex]
    exact (ConnectedComponent.sound hreach).symm

end
end StatMech.FrontierD
