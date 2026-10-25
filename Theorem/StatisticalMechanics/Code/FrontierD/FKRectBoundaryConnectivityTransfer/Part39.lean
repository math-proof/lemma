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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part41
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


theorem fkRectBoundaryConnectivityTwoLayerTransfer_diag_pos
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (state : FKRectBoundaryConnectivityState W) :
    0 < fkRectBoundaryConnectivityTwoLayerTransfer hW q state state := by
  unfold fkRectBoundaryConnectivityTwoLayerTransfer
  rw [Matrix.mul_apply]
  have hterm := mul_pos
    (fkRectBoundaryConnectivityLayerTransfer_diag_pos hW hq false state)
    (fkRectBoundaryConnectivityLayerTransfer_diag_pos hW hq true state)
  apply lt_of_lt_of_le hterm
  apply Finset.single_le_sum (fun middle _ => mul_nonneg
    (fkRectBoundaryConnectivityLayerTransfer_nonneg hW hq false state middle)
    (fkRectBoundaryConnectivityLayerTransfer_nonneg hW hq true middle state))
    (Finset.mem_univ state)


theorem fkRectBoundaryLayerTransfer_diag_pos_of_isConnectivity
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (evenRow : Bool) (state : FKRectBoundaryState W)
    (hstate : state.IsConnectivity) :
    0 < fkRectBoundaryLayerTransfer hW q evenRow state state := by
  let vertical : Bool × Fin W -> Bool := fkRectBoundaryVerticalLayer
  have houtput : fkRectBoundaryLayerOutput hW evenRow state vertical = state :=
    fkRectBoundaryLayerOutput_vertical hW evenRow state hstate
  have hterm : 0 <
      (if fkRectBoundaryLayerOutput hW evenRow state vertical = state then
        fkRectBoundaryLayerWeight hW q evenRow state vertical else 0) := by
    rw [if_pos houtput]
    exact fkRectBoundaryLayerWeight_pos hW hq evenRow state vertical
  apply lt_of_lt_of_le hterm
  unfold fkRectBoundaryLayerTransfer
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun eta : Bool × Fin W -> Bool =>
      if fkRectBoundaryLayerOutput hW evenRow state eta = state then
        fkRectBoundaryLayerWeight hW q evenRow state eta else 0)
    (fun eta _ => by
      dsimp only
      split_ifs
      · exact (fkRectBoundaryLayerWeight_pos hW hq evenRow state eta).le
      · exact le_rfl)
    (Finset.mem_univ vertical)

theorem fkRectBoundaryTwoLayerTransfer_diag_pos_of_isConnectivity
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (state : FKRectBoundaryState W) (hstate : state.IsConnectivity) :
    0 < fkRectBoundaryTwoLayerTransfer hW q state state := by
  unfold fkRectBoundaryTwoLayerTransfer
  rw [Matrix.mul_apply]
  have hterm := mul_pos
    (fkRectBoundaryLayerTransfer_diag_pos_of_isConnectivity
      hW hq false state hstate)
    (fkRectBoundaryLayerTransfer_diag_pos_of_isConnectivity
      hW hq true state hstate)
  apply lt_of_lt_of_le hterm
  exact Finset.single_le_sum
    (fun middle _ => mul_nonneg
      (fkRectBoundaryLayerTransfer_nonneg hW hq false state middle)
      (fkRectBoundaryLayerTransfer_nonneg hW hq true middle state))
    (Finset.mem_univ state)


theorem fkRectBoundaryTwoLayerTransfer_reachable_isConnectivity
    {W : Nat} (hW : 0 < W) {q : Real} (hq : 0 < q)
    (state : FKRectBoundaryState W)
    (hreach : MatrixPositiveReachable
      (fkRectBoundaryTwoLayerTransfer hW q)
      (fkRectBoundaryInitialState W) state) :
    state.IsConnectivity := by
  classical
  obtain ⟨n, hn⟩ := hreach
  cases n with
  | zero =>
      have heq : fkRectBoundaryInitialState W = state := by
        by_contra hne
        simp [hne] at hn
      subst state
      exact fkRectBoundaryInitialState_isConnectivity W
  | succ n =>
      rw [pow_succ, Matrix.mul_apply, Finset.sum_pos_iff_of_nonneg] at hn
      · obtain ⟨middle, hmiddle, hproduct⟩ := hn
        have htransition :
            0 < fkRectBoundaryTwoLayerTransfer hW q middle state := by
          have hleft := Matrix.pow_apply_nonneg
            (fkRectBoundaryTwoLayerTransfer_nonneg hW hq) n
            (fkRectBoundaryInitialState W) middle
          have hright := fkRectBoundaryTwoLayerTransfer_nonneg
            hW hq middle state
          nlinarith
        exact fkRectBoundaryTwoLayerTransfer_target_isConnectivity_of_pos
          hW hq middle state htransition
      · intro middle hmiddle
        exact mul_nonneg
          (Matrix.pow_apply_nonneg
            (fkRectBoundaryTwoLayerTransfer_nonneg hW hq) n
            (fkRectBoundaryInitialState W) middle)
          (fkRectBoundaryTwoLayerTransfer_nonneg hW hq middle state)


theorem fkRectBoundaryLayerTransfer_mulVec {W : Nat} (hW : 0 < W)
    (q : Real) (evenRow : Bool) (f : FKRectBoundaryState W -> Real)
    (source : FKRectBoundaryState W) :
    (fkRectBoundaryLayerTransfer hW q evenRow *ᵥ f) source =
      ∑ eta : Bool × Fin W -> Bool,
        fkRectBoundaryLayerWeight hW q evenRow source eta *
          f (fkRectBoundaryLayerOutput hW evenRow source eta) := by
  classical
  rw [Matrix.mulVec, dotProduct]
  unfold fkRectBoundaryLayerTransfer
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro eta heta
  simp


theorem fkRectBoundaryTwoLayerTransfer_mulVec {W : Nat} (hW : 0 < W)
    (q : Real) (f : FKRectBoundaryState W -> Real)
    (source : FKRectBoundaryState W) :
    (fkRectBoundaryTwoLayerTransfer hW q *ᵥ f) source =
      ∑ oddLayer : Bool × Fin W -> Bool,
        fkRectBoundaryLayerWeight hW q false source oddLayer *
          ∑ evenLayer : Bool × Fin W -> Bool,
            fkRectBoundaryLayerWeight hW q true
                (fkRectBoundaryLayerOutput hW false source oddLayer)
                evenLayer *
              f (fkRectBoundaryLayerOutput hW true
                (fkRectBoundaryLayerOutput hW false source oddLayer)
                evenLayer) := by
  rw [fkRectBoundaryTwoLayerTransfer, ← Matrix.mulVec_mulVec,
    fkRectBoundaryLayerTransfer_mulVec]
  apply Finset.sum_congr rfl
  intro oddLayer hodd
  rw [fkRectBoundaryLayerTransfer_mulVec]

theorem fkRectBoundarySeamFunctional_pos {W : Nat} (hW : 0 < W)
    {q : Real} (hq : 0 < q) (state : FKRectBoundaryState W) :
    0 < fkRectBoundarySeamFunctional hW q state := by
  classical
  unfold fkRectBoundarySeamFunctional fkRectBoundarySeamWeight
  exact Finset.sum_pos
    (fun eta _ => mul_pos (pow_pos (Real.sqrt_pos.2 hq) _)
      (pow_pos hq _))
    Finset.univ_nonempty


theorem fkRectBoundaryFinalFunctional_pos {W : Nat} (hW : 0 < W)
    {q : Real} (hq : 0 < q) (state : FKRectBoundaryState W) :
    0 < (fkRectBoundaryLayerTransfer hW q false *ᵥ
      fkRectBoundarySeamFunctional hW q) state := by
  rw [fkRectBoundaryLayerTransfer_mulVec]
  exact Finset.sum_pos
    (fun eta _ => mul_pos
      (fkRectBoundaryLayerWeight_pos hW hq false state eta)
      (fkRectBoundarySeamFunctional_pos hW hq
        (fkRectBoundaryLayerOutput hW false state eta)))
    Finset.univ_nonempty


end
end StatMech.FrontierD
