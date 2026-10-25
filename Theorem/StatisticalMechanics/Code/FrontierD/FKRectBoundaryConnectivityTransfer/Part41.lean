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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part43
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundaryListCoefficientSum_alternating
    {W : Nat} (hW : 0 < W) (q : Real)
    (state : FKRectBoundaryState W) (blocks : Nat) :
    fkRectBoundaryListCoefficientSum hW q state
        (fkRectBoundaryAlternatingParityList blocks) =
      fkRectBoundaryAlternatingCoefficientSum hW q state blocks := by
  induction blocks generalizing state with
  | zero => rfl
  | succ blocks ih =>
      simp only [fkRectBoundaryAlternatingParityList,
        fkRectBoundaryListCoefficientSum,
        fkRectBoundaryAlternatingCoefficientSum]
      apply Finset.sum_congr rfl
      intro oddLayer hodd
      apply congrArg (fun x =>
        fkRectBoundaryLayerWeight hW q false state oddLayer * x)
      apply Finset.sum_congr rfl
      intro evenLayer heven
      rw [ih]


theorem fkRectBoundaryAlternatingCoefficientSum_eq_matrix
    {W : Nat} (hW : 0 < W) (q : Real)
    (state : FKRectBoundaryState W) (blocks : Nat) :
    fkRectBoundaryAlternatingCoefficientSum hW q state blocks =
      ((((fkRectBoundaryTwoLayerTransfer hW q) ^ blocks *
          fkRectBoundaryLayerTransfer hW q false) *ᵥ
          fkRectBoundarySeamFunctional hW q) state) := by
  induction blocks generalizing state with
  | zero =>
      simp only [fkRectBoundaryAlternatingCoefficientSum, pow_zero, one_mul]
      symm
      exact fkRectBoundaryLayerTransfer_mulVec hW q false _ _
  | succ blocks ih =>
      rw [fkRectBoundaryAlternatingCoefficientSum]
      rw [pow_succ']
      rw [Matrix.mul_assoc]
      rw [← Matrix.mulVec_mulVec]
      rw [fkRectBoundaryTwoLayerTransfer_mulVec]
      apply Finset.sum_congr rfl
      intro oddLayer hodd
      apply congrArg (fun x =>
        fkRectBoundaryLayerWeight hW q false state oddLayer * x)
      apply Finset.sum_congr rfl
      intro evenLayer heven
      rw [ih]


theorem fkRectBoundaryTransferReducedZ_eq_coefficientSum
    {W : Nat} (hW : 0 < W) (q : Real) (blocks : Nat) :
    fkRectBoundaryTransferReducedZ hW q blocks =
      fkRectBoundaryAlternatingCoefficientSum hW q
        (fkRectBoundaryInitialState W) blocks := by
  symm
  exact fkRectBoundaryAlternatingCoefficientSum_eq_matrix
    hW q (fkRectBoundaryInitialState W) blocks


theorem fkRectCriticalReducedZ_eq_boundaryTransferReducedZ
    (R : FKRectTorus) (q : Real) (blocks : Nat)
    (hheight : R.height = 2 * (blocks + 1)) :
    fkRectCriticalReducedZ R q =
      fkRectBoundaryTransferReducedZ R.width_pos q blocks := by
  unfold fkRectCriticalReducedZ
  calc
    (∑ omega : R.Configuration,
        fkRectCriticalReducedWeight R q omega) =
        ∑ omega : R.Configuration,
          fkRectBoundaryTransferCoefficient R q omega := by
            apply Finset.sum_congr rfl
            intro omega homega
            exact (fkRectBoundaryTransferCoefficient_eq_criticalReducedWeight
              R q omega).symm
    _ = ∑ layers : Fin (R.height - 1) ->
          Bool × Fin R.width -> Bool,
        fkRectBoundaryRunWeight R.width_pos q
            (fkRectBoundaryInitialState R.width)
            (List.ofFn fun i : Fin (R.height - 1) =>
              (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                layers i)) *
          fkRectBoundarySeamFunctional R.width_pos q
            (fkRectBoundaryRunState R.width_pos
              (fkRectBoundaryInitialState R.width)
              (List.ofFn fun i : Fin (R.height - 1) =>
                (decide (Even (fkRectBoundaryNonSeamRow R i).val),
                  layers i))) :=
            sum_fkRectBoundaryTransferCoefficient_eq_layerSum R q
    _ = fkRectBoundaryListCoefficientSum R.width_pos q
          (fkRectBoundaryInitialState R.width)
          (List.ofFn fun i : Fin (R.height - 1) =>
            decide (Even (fkRectBoundaryNonSeamRow R i).val)) :=
            fkRectBoundaryFiniteLayerSum_eq_listCoefficientSum
              R.width_pos q (fkRectBoundaryInitialState R.width)
              (R.height - 1)
              (fun i => decide
                (Even (fkRectBoundaryNonSeamRow R i).val))
    _ = fkRectBoundaryAlternatingCoefficientSum R.width_pos q
          (fkRectBoundaryInitialState R.width) blocks := by
            rw [fkRect_nonSeamParityList_eq_alternating R blocks hheight,
              fkRectBoundaryListCoefficientSum_alternating]
    _ = fkRectBoundaryTransferReducedZ R.width_pos q blocks := by
            rw [fkRectBoundaryTransferReducedZ_eq_coefficientSum]

@[simp] theorem fkRectBoundaryTransferReducedZ_zero {W : Nat} (hW : 0 < W)
    (q : Real) :
    fkRectBoundaryTransferReducedZ hW q 0 =
      ∑ oddLayer : Bool × Fin W -> Bool,
        fkRectBoundaryLayerWeight hW q false
            (fkRectBoundaryInitialState W) oddLayer *
          fkRectBoundarySeamFunctional hW q
            (fkRectBoundaryLayerOutput hW false
              (fkRectBoundaryInitialState W) oddLayer) := by
  simp only [fkRectBoundaryTransferReducedZ, pow_zero, one_mul]
  exact fkRectBoundaryLayerTransfer_mulVec hW q false _ _

end
end StatMech.FrontierD
