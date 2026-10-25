/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part34
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


@[simp] theorem fkRectConfigurationScheduleEquiv_fst
    (R : FKRectTorus) (omega : R.Configuration) :
    (fkRectConfigurationScheduleEquiv R omega).1 =
      fkRectConfigurationLayer R omega (fkRectBoundarySeamRow R) := by
  funext a
  rfl

@[simp] theorem fkRectConfigurationScheduleEquiv_snd
    (R : FKRectTorus) (omega : R.Configuration)
    (i : Fin (R.height - 1)) :
    (fkRectConfigurationScheduleEquiv R omega).2 i =
      fkRectConfigurationLayer R omega (fkRectBoundaryNonSeamRow R i) := by
  funext a
  rfl

@[simp] theorem fkRectConfigurationScheduleEquiv_symm_seam
    (R : FKRectTorus) (seam : Bool × Fin R.width -> Bool)
    (layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool) :
    fkRectConfigurationLayer R
        ((fkRectConfigurationScheduleEquiv R).symm (seam, layers))
        (fkRectBoundarySeamRow R) = seam := by
  have h := congrArg Prod.fst
    ((fkRectConfigurationScheduleEquiv R).apply_symm_apply (seam, layers))
  change (fkRectConfigurationScheduleEquiv R
    ((fkRectConfigurationScheduleEquiv R).symm (seam, layers))).1 = seam at h
  rw [fkRectConfigurationScheduleEquiv_fst] at h
  exact h

@[simp] theorem fkRectConfigurationScheduleEquiv_symm_nonSeam
    (R : FKRectTorus) (seam : Bool × Fin R.width -> Bool)
    (layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool)
    (i : Fin (R.height - 1)) :
    fkRectConfigurationLayer R
        ((fkRectConfigurationScheduleEquiv R).symm (seam, layers))
        (fkRectBoundaryNonSeamRow R i) = layers i := by
  have h := congrArg (fun p => p.2 i)
    ((fkRectConfigurationScheduleEquiv R).apply_symm_apply (seam, layers))
  change (fkRectConfigurationScheduleEquiv R
    ((fkRectConfigurationScheduleEquiv R).symm (seam, layers))).2 i =
      layers i at h
  rw [fkRectConfigurationScheduleEquiv_snd] at h
  exact h

theorem fkRectBoundaryTransferCoefficient_schedule_symm
    (R : FKRectTorus) (q : Real)
    (seam : Bool × Fin R.width -> Bool)
    (layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool) :
    fkRectBoundaryTransferCoefficient R q
        ((fkRectConfigurationScheduleEquiv R).symm (seam, layers)) =
      fkRectBoundaryRunWeight R.width_pos q
          (fkRectBoundaryInitialState R.width)
          (List.ofFn fun i : Fin (R.height - 1) =>
            (decide (Even (fkRectBoundaryNonSeamRow R i).val), layers i)) *
        fkRectBoundarySeamWeight R.width_pos q
          (fkRectBoundaryRunState R.width_pos
            (fkRectBoundaryInitialState R.width)
            (List.ofFn fun i : Fin (R.height - 1) =>
              (decide (Even (fkRectBoundaryNonSeamRow R i).val), layers i)))
          seam := by
  simp [fkRectBoundaryTransferCoefficient,
    fkRectConfigurationFinalBoundaryState,
    fkRectConfigurationNonSeamLayers]

theorem sum_fkRectBoundaryTransferCoefficient_eq_layerSum
    (R : FKRectTorus) (q : Real) :
    (∑ omega : R.Configuration,
      fkRectBoundaryTransferCoefficient R q omega) =
    ∑ layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool,
      fkRectBoundaryRunWeight R.width_pos q
          (fkRectBoundaryInitialState R.width)
          (List.ofFn fun i : Fin (R.height - 1) =>
            (decide (Even (fkRectBoundaryNonSeamRow R i).val), layers i)) *
        fkRectBoundarySeamFunctional R.width_pos q
          (fkRectBoundaryRunState R.width_pos
            (fkRectBoundaryInitialState R.width)
            (List.ofFn fun i : Fin (R.height - 1) =>
              (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                layers i))) := by
  classical
  calc
    (∑ omega : R.Configuration,
        fkRectBoundaryTransferCoefficient R q omega) =
        ∑ p : (Bool × Fin R.width -> Bool) ×
            (Fin (R.height - 1) -> Bool × Fin R.width -> Bool),
          fkRectBoundaryTransferCoefficient R q
            ((fkRectConfigurationScheduleEquiv R).symm p) := by
              apply Fintype.sum_equiv (fkRectConfigurationScheduleEquiv R)
              intro omega
              simp
    _ = ∑ seam : Bool × Fin R.width -> Bool,
        ∑ layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool,
          fkRectBoundaryRunWeight R.width_pos q
              (fkRectBoundaryInitialState R.width)
              (List.ofFn fun i : Fin (R.height - 1) =>
                (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                  layers i)) *
            fkRectBoundarySeamWeight R.width_pos q
              (fkRectBoundaryRunState R.width_pos
                (fkRectBoundaryInitialState R.width)
                (List.ofFn fun i : Fin (R.height - 1) =>
                  (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                    layers i))) seam := by
              rw [Fintype.sum_prod_type]
              apply Finset.sum_congr rfl
              intro seam hseam
              apply Finset.sum_congr rfl
              intro layers hlayers
              exact fkRectBoundaryTransferCoefficient_schedule_symm
                R q seam layers
    _ = ∑ layers : Fin (R.height - 1) -> Bool × Fin R.width -> Bool,
        ∑ seam : Bool × Fin R.width -> Bool,
          fkRectBoundaryRunWeight R.width_pos q
              (fkRectBoundaryInitialState R.width)
              (List.ofFn fun i : Fin (R.height - 1) =>
                (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                  layers i)) *
            fkRectBoundarySeamWeight R.width_pos q
              (fkRectBoundaryRunState R.width_pos
                (fkRectBoundaryInitialState R.width)
                (List.ofFn fun i : Fin (R.height - 1) =>
                  (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                    layers i))) seam := by
              rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro layers hlayers
      rw [← Finset.mul_sum]
      rfl


end
end StatMech.FrontierD
