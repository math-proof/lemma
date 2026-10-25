/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailBlockBounds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailClosedBall.Part4
import Def.StatisticalMechanics.Code.Exact3D.FinitePlusTailBlockBounds.Part5


namespace StatMech

namespace Exact3D

namespace FinitePlusTailBlockBounds

variable {n : ℕ} {α : Type*}


@[simp] theorem toClosedBallCertificateOfComponentResiduals_contraction
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).contraction =
        B.toLipschitzCertificate hc_nonneg hc_lt_one
          hfinite_column_sum_le htail_column_sum_le :=
  rfl

@[simp] theorem toClosedBallCertificateOfComponentResiduals_center
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).center = center :=
  rfl

@[simp] theorem toClosedBallCertificateOfComponentResiduals_radius
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).radius = radius :=
  rfl

@[simp] theorem toClosedBallCertificateOfComponentResiduals_residual
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).residual = finiteResidual + tailResidual :=
  rfl


theorem toClosedBallCertificateOfComponentResiduals_fixedPoint_mem
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    FinitePlusTailState.ClosedBall center radius
      (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius hfinite
        htail hbudget).fixedPoint := by
  simpa using
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).fixedPoint_mem


theorem toClosedBallCertificateOfComponentResiduals_fixedPoint_isFixed
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    B.map
      (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius hfinite
        htail hbudget).fixedPoint =
      (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius hfinite
        htail hbudget).fixedPoint := by
  simpa using
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).fixedPoint_isFixed


theorem toClosedBallCertificateOfComponentResiduals_exists_unique_fixedPoint
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    ∃! p : FinitePlusTailState n α,
      (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
        hfinite_column_sum_le htail_column_sum_le center hradius hfinite
        htail hbudget).contraction.map p = p :=
  (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
    hfinite_column_sum_le htail_column_sum_le center hradius hfinite
    htail hbudget).exists_unique_fixedPoint


theorem toClosedBallCertificateOfComponentResiduals_mapsClosedBall
    (B : FinitePlusTailBlockBounds n α)
    {c : ℝ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hfinite_column_sum_le : B.finiteToFinite + B.finiteToTail ≤ c)
    (htail_column_sum_le : B.tailToFinite + B.tailToTail ≤ c)
    (center : FinitePlusTailState n α) {radius finiteResidual tailResidual : ℝ}
    (hradius : 0 ≤ radius)
    (hfinite :
      FiniteContraction.l1Dist (B.finiteMap center) center.finite ≤
        finiteResidual)
    (htail : (B.tailMap center).dist center.tail ≤ tailResidual)
    (hbudget : finiteResidual + tailResidual + c * radius ≤ radius) :
    FinitePlusTailState.MapsClosedBall B.map center radius := by
  simpa [toClosedBallCertificateOfComponentResiduals] using
    (B.toClosedBallCertificateOfComponentResiduals hc_nonneg hc_lt_one
      hfinite_column_sum_le htail_column_sum_le center hradius hfinite
      htail hbudget).mapsClosedBall


end FinitePlusTailBlockBounds
end Exact3D
end StatMech
