/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/MatrixCertificate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Exact3D.Intervals.Part12
import Structure.StatisticalMechanics.Code.Exact3D.MatrixCertificate


namespace StatMech

namespace Exact3D

namespace RatInterval

def RowSumContraction.with_larger_constant {n : ℕ}
    {I : IntervalMatrix n n} (hI : RowSumContraction I) {c' : ℚ}
    (hc : hI.c ≤ c') (hc_lt_one : c' < 1) :
    RowSumContraction I where
  c := c'
  c_nonneg := le_trans hI.c_nonneg hc
  c_lt_one := hc_lt_one
  row_bound := fun i => le_trans (hI.row_bound i) hc


def ColumnSumContraction.with_larger_constant {n : ℕ}
    {I : IntervalMatrix n n} (hI : ColumnSumContraction I) {c' : ℚ}
    (hc : hI.c ≤ c') (hc_lt_one : c' < 1) :
    ColumnSumContraction I where
  c := c'
  c_nonneg := le_trans hI.c_nonneg hc
  c_lt_one := hc_lt_one
  col_bound := fun j => le_trans (hI.col_bound j) hc


def rowSumContraction_of_pointMatrix {n : ℕ} (A : Fin n → Fin n → ℚ)
    {c : ℚ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hrow : ∀ i, (∑ j, |A i j|) ≤ c) :
    RowSumContraction (pointMatrix A) where
  c := c
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  row_bound := by
    intro i
    simpa [MatrixAbsRowSum_pointMatrix] using hrow i


def columnSumContraction_of_pointMatrix {n : ℕ} (A : Fin n → Fin n → ℚ)
    {c : ℚ} (hc_nonneg : 0 ≤ c) (hc_lt_one : c < 1)
    (hcol : ∀ j, (∑ i, |A i j|) ≤ c) :
    ColumnSumContraction (pointMatrix A) where
  c := c
  c_nonneg := hc_nonneg
  c_lt_one := hc_lt_one
  col_bound := by
    intro j
    simpa [MatrixAbsColSum_pointMatrix] using hcol j


end RatInterval
end Exact3D
end StatMech
