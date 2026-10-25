/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingLevelPlateau.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingCutCollision
import Theorem.StatisticalMechanics.Code.FrontierD.IntegerUnitStepPlateau
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem fkRectMedialBoundaryPrimalSeamTrace_add
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (m n : Nat) :
    fkRectMedialBoundaryPrimalSeamTrace R pairing d (m + n) =
      fkRectMedialBoundaryPrimalSeamTrace R pairing d m +
        fkRectMedialBoundaryPrimalSeamTrace R pairing
          ((fkMedialBoundaryStep pairing)^[m] d) n := by
  induction m generalizing d with
  | zero =>
      simp [fkRectMedialBoundaryPrimalSeamTrace]
  | succ m ih =>
      simp only [Nat.succ_add, fkRectMedialBoundaryPrimalSeamTrace]
      rw [ih]
      rw [Function.iterate_succ_apply]
      apply Prod.ext <;> simp only [Prod.fst_add, Prod.snd_add] <;> ring


theorem fkRectMedialBoundaryPrimalSeamTrace_succ
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) (m : Nat) :
    fkRectMedialBoundaryPrimalSeamTrace R pairing d (m + 1) =
      fkRectMedialBoundaryPrimalSeamTrace R pairing d m +
        fkRectMedialBoundaryPrimalSeamIncrement R pairing
          ((fkMedialBoundaryStep pairing)^[m] d) := by
  rw [fkRectMedialBoundaryPrimalSeamTrace_add]
  simp [fkRectMedialBoundaryPrimalSeamTrace]


theorem fkRectVerticalSeamIncrement_bounds
    (R : FKRectTorus) (x y : R.Vertex) :
    -1 ≤ fkRectVerticalSeamIncrement R x y ∧
      fkRectVerticalSeamIncrement R x y ≤ 1 := by
  unfold fkRectVerticalSeamIncrement
  split
  · norm_num
  · split <;> norm_num


theorem fkRectBlackBoundaryPrefixVerticalLevel_unitSteps
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    IntUnitSteps (fun m =>
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2) := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  change IntUnitSteps (fun m =>
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2)
  intro m
  have hsucc := fkRectMedialBoundaryPrimalSeamTrace_succ
    R pairing d.1 m
  have hbound := fkRectVerticalSeamIncrement_bounds R
    (fkRectMedialDartPrimalLabel R
      ((fkMedialBoundaryStep pairing)^[m] d.1))
    (fkRectMedialDartPrimalLabel R
      (fkMedialBoundaryStep pairing
        ((fkMedialBoundaryStep pairing)^[m] d.1)))
  change -1 ≤
      (fkRectMedialBoundaryPrimalSeamIncrement R pairing
        ((fkMedialBoundaryStep pairing)^[m] d.1)).2 ∧
    (fkRectMedialBoundaryPrimalSeamIncrement R pairing
      ((fkMedialBoundaryStep pairing)^[m] d.1)).2 ≤ 1 at hbound
  have hsnd := congrArg Prod.snd hsucc
  simp only [Prod.snd_add] at hsnd
  change
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (m + 1)).2 ≤
        (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 + 1 ∧
      (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 ≤
        (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (m + 1)).2 + 1
  constructor <;> omega


theorem fkRectBlackBoundaryPrimalSeamTrace_two_mul_length_snd
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    let n := (fkRectBlackOrbitList pairing d).length
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 (2 * n)).2 =
      2 * (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := (fkRectBlackOrbitList pairing d).length
  have hblack : (fkMedialBlackBoundaryPerm pairing)^[n] d = d :=
    fkRectBlackBoundaryPerm_pow_length_apply pairing d
  have hdart : (fkMedialBoundaryStep pairing)^[n] d.1 = d.1 := by
    rw [← fkMedialBlackBoundaryPerm_iterate_val pairing d n, hblack]
  have hadd := fkRectMedialBoundaryPrimalSeamTrace_add
    R pairing d.1 n n
  rw [hdart] at hadd
  have hwind := fkRectBlackBoundaryPrimalCycleWalk_winding R omega d
  change fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d) =
    fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 n at hwind
  have hsnd := congrArg Prod.snd hadd
  simp only [Prod.snd_add] at hsnd
  rw [show 2 * n = n + n by omega, hsnd, ← hwind]
  ring


theorem exists_fkRectBlackBoundaryUnitPlateauEndpoints
    (R : FKRectTorus) (omega : R.Configuration)
    (d : FKMedialBlackDart R.medialTorus)
    (hpos : 0 < (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2)
    (j : Fin (fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat) :
    let pairing := fkRectConfigurationToMedialPairing R omega
    let n := (fkRectBlackOrbitList pairing d).length
    let r : Int := j.val + 1
    ∃ ab : Nat × Nat,
      0 < ab.1 ∧ ab.1 ≤ ab.2 ∧ ab.2 < 2 * n ∧
        (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1
          (ab.1 - 1)).2 = r - 1 ∧
        (∀ m, ab.1 ≤ m → m ≤ ab.2 →
          (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 = r) ∧
        (∀ m < ab.2 + 1,
          (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2 < r + 1) ∧
        (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1
          (ab.2 + 1)).2 = r + 1 := by
  dsimp only
  let pairing := fkRectConfigurationToMedialPairing R omega
  let n := (fkRectBlackOrbitList pairing d).length
  let f : Nat → Int := fun m =>
    (fkRectMedialBoundaryPrimalSeamTrace R pairing d.1 m).2
  have hunit : IntUnitSteps f := by
    exact fkRectBlackBoundaryPrefixVerticalLevel_unitSteps R omega d
  have hzero : f 0 = 0 := rfl
  let r : Int := j.val + 1
  have hr : 0 < r := by simp [r]
  have hk : ((fkRectWalkWinding R
      (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat : Int) =
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
    rw [Int.toNat_of_nonneg hpos.le]
  have hj : (j.val : Int) + 1 ≤
      (fkRectWalkWinding R
        (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2 := by
    calc
      (j.val : Int) + 1 ≤
          ((fkRectWalkWinding R
            (fkRectBlackBoundaryPrimalCycleWalk R omega d)).2.toNat : Int) := by
        exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
      _ = _ := hk
  have hreach : r + 1 ≤ f (2 * n) := by
    dsimp [f, n, pairing]
    rw [fkRectBlackBoundaryPrimalSeamTrace_two_mul_length_snd]
    dsimp [r]
    omega
  rcases exists_intUnitStep_bracketedPlateau hunit hzero hr hreach with
    ⟨a, b, hs⟩
  exact ⟨(a, b), hs⟩


end
end StatMech.FrontierD
