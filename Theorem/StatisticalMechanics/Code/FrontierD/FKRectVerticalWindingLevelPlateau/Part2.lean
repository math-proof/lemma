/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutCollision
import Theorem.StatisticalMechanics.Code.FrontierD.IntegerUnitStepPlateau
import Def.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingLevelPlateau
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectBlackBoundaryUnitPlateauEndpoints_spec
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (j : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    let n := (fkRectBlackOrbitList pairing d).length
    let ab := fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j
    let r : Int := j.val + 1
    0 < ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 < 2 * n ∧
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1
        (ab.1 - 1)).2 = r - 1 ∧
      (∀ m, ab.1 ≤ m → m ≤ ab.2 →
        (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 = r) ∧
      (∀ m < ab.2 + 1,
        (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 < r + 1) ∧
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1
        (ab.2 + 1)).2 = r + 1 := by
  exact Classical.choose_spec
    (exists_fkRectBlackBoundaryUnitPlateauEndpoints R omega d hpos j)


theorem fkRectMedialBoundaryPrimalStep_cutReachable_of_snd_eq_zero
    (R : FKRectTorus) (omega : R.Configuration)
    (e : FKMedialDart R.medialTorus)
    (hzero : (fkRectMedialBoundaryPrimalSeamIncrement R
      (fkRectConfigurationToMedialPairing R omega) e).2 = 0) :
    (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).Reachable
        (fkRectMedialDartPrimalLabel R e)
        (fkRectMedialDartPrimalLabel R
          (fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega) e)) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  rcases fkRectMedialDartPrimalLabel_boundaryStep_eq_or_adj
      R omega e with heq | hadj
  · rw [heq]
  · apply (fkRectForceHorizontalCutClosed_adj_of_not_crossesVerticalSeam
      R omega hadj ?_).reachable
    intro hcross
    exact (fkRectVerticalSeamIncrement_ne_zero_of_crosses
      R _ _ hcross) hzero


theorem fkRectBlackBoundaryPlateau_cutReachable
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) {a b : Nat}
    (hab : a ≤ b)
    (hconst : ∀ m, a ≤ m → m ≤ b →
      (fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d.1 m).2 =
      (fkRectMedialBoundaryPrimalSeamTrace R
        (fkRectConfigurationToMedialPairing R omega) d.1 a).2) :
    (fkRectOpenGraph R
      (fkRectForceHorizontalCutClosed R omega)).Reachable
        (fkRectMedialDartPrimalLabel R
          ((fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega))^[a] d.1))
        (fkRectMedialDartPrimalLabel R
          ((fkMedialBoundaryStep
            (fkRectConfigurationToMedialPairing R omega))^[b] d.1)) := by
  let pairing := fkRectConfigurationToMedialPairing R omega
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  induction k with
  | zero => exact Reachable.refl _
  | succ k ih =>
      have hprefix := fkRectMedialBoundaryPrimalSeamTrace_succ
        R pairing d.1 (a + k)
      have hlevel0 := hconst (a + k) (by omega) (by omega)
      have hlevel1 := hconst (a + k + 1) (by omega) (by omega)
      change (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1
        (a + k)).2 = _ at hlevel0
      change (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1
        (a + k + 1)).2 = _ at hlevel1
      have hinc : (fkRectMedialBoundaryPrimalSeamIncrement R pairing
          ((fkMedialBoundaryStep pairing)^[a + k] d.1)).2 = 0 := by
        have hsnd := congrArg Prod.snd hprefix
        simp only [Prod.snd_add] at hsnd
        omega
      have hreach :=
        fkRectMedialBoundaryPrimalStep_cutReachable_of_snd_eq_zero
          R omega ((fkMedialBoundaryStep pairing)^[a + k] d.1) hinc
      have hreach' :
          (fkRectOpenGraph R
            (fkRectForceHorizontalCutClosed R omega)).Reachable
              (fkRectMedialDartPrimalLabel R
                ((fkMedialBoundaryStep pairing)^[a + k] d.1))
              (fkRectMedialDartPrimalLabel R
                ((fkMedialBoundaryStep pairing)^[a + (k + 1)] d.1)) := by
        rw [show a + (k + 1) = (a + k) + 1 by omega,
          Function.iterate_succ_apply']
        exact hreach
      exact (ih (by omega)
        (fun m ham hmk => hconst m ham (by omega))).trans hreach'


theorem fkRectVerticalSeamIncrement_eq_one_endpoints
    (R : FKRectTorus) (x y : R.Vertex)
    (hinc : fkRectVerticalSeamIncrement R x y = 1) :
    x.2 = fkRectTopRow R ∧ y.2 = fkRectBottomRow R := by
  unfold fkRectVerticalSeamIncrement at hinc
  split at hinc
  · rename_i h
    constructor
    · apply Fin.ext
      simp [fkRectTopRow]
      omega
    · apply Fin.ext
      simp [fkRectBottomRow]
      omega
  · split at hinc <;> norm_num at hinc


end
end StatMech.FrontierD
