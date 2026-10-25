/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectZeroTurnMixedCandidates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.FKRectMedialDualShift.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedAnnulusCharge
import Def.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnMixedCandidates
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectRefinedBoundaryCenterAfter_dualShift
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) (c : Int × Int) (n : Nat) :
    fkRectRefinedBoundaryCenterAfter
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega))
        (fkRectMedialDualShiftDart R d) c n =
      fkRectRefinedBoundaryCenterAfter
        (fkRectConfigurationToMedialPairing R omega) d c n := by
  induction n generalizing d c with
  | zero => rfl
  | succ n ih =>
      simp only [fkRectRefinedBoundaryCenterAfter]
      rw [← fkRectMedialDualShiftDart_boundaryStep]
      have hlocal := fkRectMedialDualShiftDart_localMate R omega d
      have hside := congrArg
        (fun e : FKMedialDart R.medialTorus => e.2) hlocal
      change (fkMedialLocalMate
          (fkRectConfigurationToMedialPairing R omega) d).2 =
        (fkMedialLocalMate
          (fkRectConfigurationToMedialPairing R
            (fkRectDualConfigurationEquiv R omega))
          (fkRectMedialDualShiftDart R d)).2 at hside
      rw [hside]
      exact ih _ _


theorem fkRectMedialBoundaryPrimalSeamTrace_dualShift
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialDart R.medialTorus) (n : Nat)
    (hclosed : (fkMedialBoundaryStep
      (fkRectConfigurationToMedialPairing R omega))^[n] d = d) :
    fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R
          (fkRectDualConfigurationEquiv R omega))
        (fkRectMedialDualShiftDart R d) n =
      fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d n := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  let dualPairing := fkRectConfigurationToMedialPairing R
    (fkRectDualConfigurationEquiv R omega)
  let c := fkRectRefinedBoundaryCanonicalCenter R d
  let z := fkRectRefinedBoundaryCanonicalCenter R
    (fkRectMedialDualShiftDart R d)
  let u := fkRectMedialBoundaryPrimalSeamTrace R pairing d n
  let v := fkRectMedialBoundaryPrimalSeamTrace R dualPairing
    (fkRectMedialDualShiftDart R d) n
  have hdualClosed : (fkMedialBoundaryStep dualPairing)^[n]
      (fkRectMedialDualShiftDart R d) =
        fkRectMedialDualShiftDart R d := by
    rw [← fkRectMedialDualShiftDart_boundaryStep_iterate R omega d n,
      hclosed]
  have ho := fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    R pairing d (0, 0) n
  have hd := fkRectRefinedBoundaryCenterAfter_eq_canonical_add_deck
    R dualPairing (fkRectMedialDualShiftDart R d)
      (c.1 - z.1, c.2 - z.2) n
  simp only [Prod.fst, Prod.snd, add_zero] at ho
  change fkRectRefinedBoundaryCenterAfter pairing d c n = _ at ho
  change fkRectRefinedBoundaryCenterAfter dualPairing
      (fkRectMedialDualShiftDart R d)
      (z.1 + (c.1 - z.1), z.2 + (c.2 - z.2)) n = _ at hd
  rw [hclosed] at ho
  rw [hdualClosed] at hd
  have hs := fkRectRefinedBoundaryCenterAfter_dualShift
    R omega d c n
  change fkRectRefinedBoundaryCenterAfter dualPairing
      (fkRectMedialDualShiftDart R d) c n =
    fkRectRefinedBoundaryCenterAfter pairing d c n at hs
  have hc1 : z.1 + (c.1 - z.1) = c.1 := by ring
  have hc2 : z.2 + (c.2 - z.2) = c.2 := by ring
  rw [hc1, hc2] at hd
  have hdeck : fkRectSquareDeckTranslation R v =
      fkRectSquareDeckTranslation R u := by
    apply Prod.ext
    · have ho1 := congrArg Prod.fst ho
      have hd1 := congrArg Prod.fst hd
      have hs1 := congrArg Prod.fst hs
      simp only [Prod.fst, Prod.snd, add_zero, sub_self] at ho1 hd1 hs1
      dsimp [c, z, u, v] at ho1 hd1 hs1 ⊢
      linarith
    · have ho2 := congrArg Prod.snd ho
      have hd2 := congrArg Prod.snd hd
      have hs2 := congrArg Prod.snd hs
      simp only [Prod.fst, Prod.snd, add_zero, sub_self] at ho2 hd2 hs2
      dsimp [c, z, u, v] at ho2 hd2 hs2 ⊢
      linarith
  exact fkRectSquareDeckHom_injective R hdeck


theorem fkRectZeroTurnRemainderDualBoundaryCycleWalk_winding
    (R : FKRectTorus) (omega : R.Configuration)
    (C : FKRectZeroTurnCutRemainderComponent R omega) :
    fkRectWalkWinding R
        (fkRectZeroTurnRemainderDualBoundaryCycleWalk R omega C) =
      fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega
          (fkRectZeroTurnRemainderBlackDart R omega C)) := by
  let d := fkRectZeroTurnRemainderBlackDart R omega C
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := (fkRectBlackOrbitList pairing d).length
  have hblack : (fkMedialBlackBoundaryPerm pairing)^[n] d = d :=
    fkRectBlackBoundaryPerm_pow_length_apply pairing d
  have hclosed : (fkMedialBoundaryStep pairing)^[n] d.1 = d.1 := by
    rw [← fkMedialBlackBoundaryPerm_iterate_val pairing d n, hblack]
  unfold fkRectZeroTurnRemainderDualBoundaryCycleWalk
  rw [fkRectWalkWinding_copy,
    fkRectMedialBoundaryPrimalTrace_winding]
  change fkRectMedialBoundaryPrimalSeamTrace R
      (fkRectConfigurationToMedialPairing R
        (fkRectDualConfigurationEquiv R omega))
      (fkRectMedialDualShiftDart R d.1) n = _
  rw [fkRectMedialBoundaryPrimalSeamTrace_dualShift
    R omega d.1 n hclosed]
  exact (fkRectBlackBoundaryPrimalCycleWalk_winding R omega d).symm


end
end StatMech.FrontierD
