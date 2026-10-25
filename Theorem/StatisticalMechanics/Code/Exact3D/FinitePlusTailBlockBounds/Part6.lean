/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part6


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


@[simp] theorem toClosedBallCertificateOfFiniteResidualVector_contraction
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).contraction =
        B.toLipschitzCertificate hc_nonneg hc_lt_one
          hfinite_column_sum_le htail_column_sum_le :=
  rfl

@[simp] theorem toClosedBallCertificateOfFiniteResidualVector_center
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).center = center :=
  rfl

@[simp] theorem toClosedBallCertificateOfFiniteResidualVector_radius
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).radius = radius :=
  rfl

@[simp] theorem toClosedBallCertificateOfFiniteResidualVector_residual
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).residual =
        (RatInterval.VectorAbsSum R : ℝ) + tailResidual :=
  rfl


theorem toClosedBallCertificateOfFiniteResidualVector_fixedPoint_mem
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    FinitePlusTailState.ClosedBall center radius
      (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hfiniteResidualMem htail hbudget).fixedPoint := by
  simpa using
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).fixedPoint_mem


theorem toClosedBallCertificateOfFiniteResidualVector_fixedPoint_isFixed
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    B.map
      (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hfiniteResidualMem htail hbudget).fixedPoint =
      (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hfiniteResidualMem htail hbudget).fixedPoint := by
  simpa using
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).fixedPoint_isFixed


theorem toClosedBallCertificateOfFiniteResidualVector_exists_unique_fixedPoint
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    ∃! p : FinitePlusTailState n α,
      (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius
        hfiniteResidualMem htail hbudget).contraction.map p = p :=
  (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
    hfinite_column_sum_le htail_column_sum_le center hradius
    hfiniteResidualMem htail hbudget).exists_unique_fixedPoint


theorem toClosedBallCertificateOfFiniteResidualVector_mapsClosedBall
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius tailResidual : ℝ}
    {R : RatInterval.IntervalVector n}
    (hradius : 0 ≤ radius)
    (hfiniteResidualMem : RatInterval.VectorMem
      (fun i => B.finiteMap center i - center.finite i) R)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget :
      (RatInterval.VectorAbsSum R : ℝ) + tailResidual + c * radius ≤
        radius) :
    FinitePlusTailState.MapsClosedBall B.map center radius := by
  simpa [toClosedBallCertificateOfFiniteResidualVector,
    toClosedBallCertificateOfComponentResiduals] using
    (B.toClosedBallCertificateOfFiniteResidualVector hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius
      hfiniteResidualMem htail hbudget).mapsClosedBall

end FinitePlusTailBlockBounds
end Exact3D
end StatMech
