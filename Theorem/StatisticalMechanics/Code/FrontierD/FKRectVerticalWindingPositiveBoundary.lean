/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectVerticalWindingPositiveBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectVerticalWindingBoundarySum
open Equiv Finset


namespace StatMech.FrontierD

noncomputable section

theorem sum_fkRectBlackBoundaryWeight_eq_zero
    (R : FKRectTorus) (omega : R.Configuration) :
    (∑ d : FKMedialBlackDart R.medialTorus,
      fkRectBlackBoundaryWeight R
        (fkRectConfigurationToMedialPairing R omega) d) = 0 := by
  let f : FKMedialBlackDart R.medialTorus -> Int × Int := fun d =>
    fkRectBlackBoundaryWeight R
      (fkRectConfigurationToMedialPairing R omega) d
  let g : R.medialTorus.Vertex × Bool -> Int × Int := fun vb =>
    f ((fkMedialBlackDartEquivVertexBool R.medialTorus).symm vb)
  have hequiv : (∑ d : FKMedialBlackDart R.medialTorus, f d) =
      ∑ vb : R.medialTorus.Vertex × Bool, g vb := by
    apply Fintype.sum_equiv
      (fkMedialBlackDartEquivVertexBool R.medialTorus)
    intro d
    change f d = g ((fkMedialBlackDartEquivVertexBool R.medialTorus) d)
    unfold g
    rw [(fkMedialBlackDartEquivVertexBool
      R.medialTorus).symm_apply_apply]
  have hprod : (∑ vb : R.medialTorus.Vertex × Bool, g vb) =
      ∑ v : R.medialTorus.Vertex, ∑ b : Bool, g (v, b) :=
    Fintype.sum_prod_type g
  change (∑ d : FKMedialBlackDart R.medialTorus, f d) = 0
  rw [hequiv, hprod]
  apply Finset.sum_eq_zero
  intro v _
  rw [Fintype.sum_bool]
  simp only [g, f, fkMedialBlackDartEquivVertexBool]
  simpa only [add_comm] using
    fkRectBlackBoundaryWeight_dart0_add_dart1_eq_zero R omega v


theorem sum_fkRectBlackBoundaryCycleWinding_eq_zero
    (R : FKRectTorus) (omega : R.Configuration) :
    (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
      fkRectBlackBoundaryCycleWinding R omega C) = 0 := by
  unfold fkRectBlackBoundaryCycleWinding
  rw [sum_permCycleQuotientWeightSum]
  exact sum_fkRectBlackBoundaryWeight_eq_zero R omega


theorem sum_fkRectBlackBoundaryCycleWinding_snd_eq_zero
    (R : FKRectTorus) (omega : R.Configuration) :
    (∑ C : FKRectConfigurationBlackBoundaryCycle R omega,
      (fkRectBlackBoundaryCycleWinding R omega C).2) = 0 := by
  have h := congrArg Prod.snd
    (sum_fkRectBlackBoundaryCycleWinding_eq_zero R omega)
  rw [Prod.snd_sum] at h
  simpa using h


end
end StatMech.FrontierD
