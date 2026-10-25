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
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part25
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


@[simp] theorem fkRectStripVertexEquiv_inl
    {W n : Nat} (v : FKRectStripVertex W n) :
    fkRectStripVertexEquiv W (n + 1) (Sum.inl v) =
      ((fkRectStripVertexEquiv W n v).1,
        (fkRectStripVertexEquiv W n v).2.castSucc) := rfl

@[simp] theorem fkRectStripVertexEquiv_inr
    {W n : Nat} (x : Fin W) :
    fkRectStripVertexEquiv W (n + 1) (Sum.inr x) =
      (x, Fin.last (n + 1)) := rfl

@[simp] theorem fkRectStripVertexEquiv_initial
    {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripVertexEquiv W n (fkRectStripInitial n x) = (x, 0) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [fkRectStripInitial, ih]

@[simp] theorem fkRectStripVertexEquiv_current
    {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripVertexEquiv W n (fkRectStripCurrent n x) =
      (x, Fin.last n) := by
  cases n with
  | zero =>
      apply Prod.ext
      · rfl
      · exact Fin.eq_zero _
  | succ n => rfl

@[simp] theorem fkRectStripVertexEquiv_boundary
    {W : Nat} (n : Nat) (u : Bool × Fin W) :
    fkRectStripVertexEquiv W n (fkRectStripBoundary n u) =
      if u.1 then (u.2, Fin.last n) else (u.2, 0) := by
  cases u with
  | mk b x => cases b <;> simp [fkRectStripBoundary]


end
end StatMech.FrontierD
