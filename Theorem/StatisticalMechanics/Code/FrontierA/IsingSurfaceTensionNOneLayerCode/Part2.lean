/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionNOneLayerCode.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneRawGenerated
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionNOneLayerCode.Part2
open Finset


namespace StatMech.FrontierA.NOneSymmetricMeanCertificate

open StatMech StatMech.Ising


theorem oddPrismTransferBridgeRawMoment_one_eq_codeSum
    (beta r : Real) :
    oddPrismTransferBridgeRawMoment beta 1 r =
      nOneTransferBridgeRawMomentCodeSum beta r := by
  unfold oddPrismTransferBridgeRawMoment
    nOneTransferBridgeRawMomentCodeSum
  rw [← sum_nOneLayerCodeEquiv (fun s => ∑ q,
    oddPrismLowerConditionedVector beta 1 s *
      oddPrismUpperConditionedVector beta 1 q *
      oddPrismPureSeamKernel r 1 s q)]
  apply Finset.sum_congr rfl
  intro s _
  rw [← sum_nOneLayerCodeEquiv (fun q =>
    oddPrismLowerConditionedVector beta 1 (nOneLayerCodeEquiv s) *
      oddPrismUpperConditionedVector beta 1 q *
      oddPrismPureSeamKernel r 1 (nOneLayerCodeEquiv s) q)]
  apply Finset.sum_congr rfl
  intro q _
  rw [oddPrismLowerConditionedVector_nOneLayerCodeEquiv,
    oddPrismUpperConditionedVector_nOneLayerCodeEquiv,
    oddPrismPureSeamKernel_nOneLayerCodeEquiv,
    Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v _
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

end StatMech.FrontierA.NOneSymmetricMeanCertificate
