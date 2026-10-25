/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part4


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


@[simp] theorem toClosedBallCertificate_contraction
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).contraction =
        B.toLipschitzCertificate hc_nonneg hc_lt_one
          hfinite_column_sum_le htail_column_sum_le :=
  rfl

@[simp] theorem toClosedBallCertificate_center
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).center = center :=
  rfl

@[simp] theorem toClosedBallCertificate_radius
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).radius = radius :=
  rfl

@[simp] theorem toClosedBallCertificate_residual
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).residual = residual :=
  rfl


theorem toClosedBallCertificate_fixedPoint_mem
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    FinitePlusTailState.ClosedBall center radius
      (B.toClosedBallCertificate hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hresidual hbudget).fixedPoint := by
  simpa using
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).fixedPoint_mem


theorem toClosedBallCertificate_fixedPoint_isFixed
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    B.map
      (B.toClosedBallCertificate hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hresidual hbudget).fixedPoint =
      (B.toClosedBallCertificate hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hresidual hbudget).fixedPoint := by
  simpa using
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).fixedPoint_isFixed


theorem toClosedBallCertificate_exists_unique_fixedPoint
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    ∃! p : FinitePlusTailState n α,
      (B.toClosedBallCertificate hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hresidual hbudget).contraction.map p = p :=
  (B.toClosedBallCertificate hc_nonneg hc_lt_one
    hfinite_column_sum_le htail_column_sum_le center hradius
    hresidual hbudget).exists_unique_fixedPoint


theorem toClosedBallCertificate_mapsClosedBall
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius residual : ℝ}
    (hradius : 0 ≤ radius)
    (hresidual : (B.map center).dist center ≤ residual)
    (hbudget : residual + c * radius ≤ radius) :
    FinitePlusTailState.MapsClosedBall B.map center radius := by
  simpa [toClosedBallCertificate] using
    (B.toClosedBallCertificate hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hresidual hbudget).mapsClosedBall


theorem residual_bound_of_componentResiduals
    (B : FinitePlusTailBlockBounds n α)
    (center : FinitePlusTailState n α)
    {finiteResidual tailResidual : ℝ}
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual) :
    (B.map center).dist center ≤ finiteResidual + tailResidual := by
  calc
    (B.map center).dist center =
        FiniteContraction.l1Dist (B.finiteMap center) center.finite +
          (B.tailMap center).dist center.tail := rfl
    _ ≤ finiteResidual + tailResidual :=
      add_le_add hfinite htail


theorem finiteResidual_le_of_vectorMem
    (B : FinitePlusTailBlockBounds n α)
    (center : FinitePlusTailState n α)
    {R : RatInterval.IntervalVector n}
    (hR : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R) :
    FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
      (RatInterval.VectorAbsSum R : ℝ) :=
  FiniteContraction.residual_l1Dist_le_of_vectorMem
    (F := fun _ : Fin n → ℝ => B.finiteMap center)
    (center := center.finite) hR


end FinitePlusTailBlockBounds
end Exact3D
end StatMech
