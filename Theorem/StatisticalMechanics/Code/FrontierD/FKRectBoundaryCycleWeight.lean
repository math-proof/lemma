/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryCycleWeight.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.PermOrbitWeightSum
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRefinedIntersection.Part7
open Equiv Finset


namespace StatMech.FrontierD

noncomputable section

theorem fkMedialCheckerColor_localMate_eq_not
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    fkMedialCheckerColor (fkMedialLocalMate pairing d) =
      !fkMedialCheckerColor d := by
  have hne := fkMedialCheckerColor_localMate_ne pairing d
  generalize hd : fkMedialCheckerColor d = b at hne ⊢
  generalize hm : fkMedialCheckerColor
    (fkMedialLocalMate pairing d) = c at hne ⊢
  cases b <;> cases c <;> simp_all


theorem fkMedial_reachable_localMate
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d : FKMedialDart T) :
    (fkMedialLoopGraph T pairing).Reachable d
      (fkMedialLocalMate pairing d) := by
  apply SimpleGraph.Adj.reachable
  rw [fkMedialLoopGraph_adj_iff]
  exact Or.inl rfl


theorem fkMedialBoundaryStep_localMate_conj
    {T : EvenTorus} (pairing : FKMedialLoopPairing T) :
    fkMedialLocalMateEquiv pairing * fkMedialBoundaryStep pairing *
        (fkMedialLocalMateEquiv pairing)⁻¹ =
      (fkMedialBoundaryStep pairing)⁻¹ := by
  apply Equiv.ext
  intro d
  simp [fkMedialBoundaryStep, fkMedialLocalMateEquiv,
    fkMedialBondMateEquiv, fkMedialLocalMate_involutive]


theorem fkMedialBoundaryStep_sameCycle_localMate_iff
    {T : EvenTorus} (pairing : FKMedialLoopPairing T)
    (d e : FKMedialDart T) :
    (fkMedialBoundaryStep pairing).SameCycle
        (fkMedialLocalMate pairing d)
        (fkMedialLocalMate pairing e) ↔
      (fkMedialBoundaryStep pairing).SameCycle d e := by
  let tau := fkMedialLocalMateEquiv pairing
  let sigma := fkMedialBoundaryStep pairing
  have hconj : tau * sigma * tau⁻¹ = sigma⁻¹ :=
    fkMedialBoundaryStep_localMate_conj pairing
  have h := Equiv.Perm.sameCycle_conj
    (f := sigma) (g := tau) (x := tau d) (y := tau e)
  rw [hconj, Equiv.Perm.sameCycle_inv] at h
  simpa [tau, fkMedialLocalMateEquiv,
    fkMedialLocalMate_involutive] using h


theorem fkRectMedialBoundaryPrimalSeamIncrement_localMate
    (R : FKRectTorus)
    (pairing : FKMedialLoopPairing R.medialTorus)
    (d : FKMedialDart R.medialTorus) :
    fkRectMedialBoundaryPrimalSeamIncrement R pairing
        (fkMedialLocalMate pairing d) =
      -fkRectMedialBoundaryPrimalSeamIncrement R pairing d := by
  have hstart : fkRectMedialDartPrimalLabel R
        (fkMedialLocalMate pairing d) =
      fkRectMedialDartPrimalLabel R
        (fkMedialBoundaryStep pairing d) := by
    rw [fkMedialBoundaryStep_apply,
      fkRectMedialDartPrimalLabel_bondMate]
  have hend : fkRectMedialDartPrimalLabel R
        (fkMedialBoundaryStep pairing
          (fkMedialLocalMate pairing d)) =
      fkRectMedialDartPrimalLabel R d := by
    rw [fkMedialBoundaryStep_apply,
      fkMedialLocalMate_involutive,
      fkRectMedialDartPrimalLabel_bondMate]
  unfold fkRectMedialBoundaryPrimalSeamIncrement
  simp only [hstart, hend]
  apply Prod.ext
  · simp only [Prod.fst_neg]
    exact fkRectHorizontalSeamIncrement_swap R _ _
  · simp only [Prod.snd_neg]
    exact fkRectVerticalSeamIncrement_swap R _ _


end
end StatMech.FrontierD
