/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCenteredTensorTentRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicBoundaryRadialCellRegularity
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalCenteredRadialPatch.Part12
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicTensorTentMorera.Part17
import Mathlib.Topology.UnitInterval
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity.Part2


namespace StatMech.Universality

open Metric Set

open scoped unitInterval

noncomputable section

theorem complexBilinearVerticalStrip_norm_sub_le
    (a00 a10 a01 a11 a02 a12 : Complex) (x y y' D : Real)
    (hx0 : 0 <= x) (hx1 : x <= 1)
    (hy0 : 0 <= y) (hy2 : y <= 2)
    (hy0' : 0 <= y') (hy2' : y' <= 2)
    (h00_10 : norm (a10 - a00) <= D)
    (h01_11 : norm (a11 - a01) <= D)
    (h02_12 : norm (a12 - a02) <= D)
    (h00_01 : norm (a01 - a00) <= D)
    (h01_02 : norm (a02 - a01) <= D)
    (h10_11 : norm (a11 - a10) <= D)
    (h11_12 : norm (a12 - a11) <= D) :
    norm (complexBilinearVerticalStrip a00 a10 a01 a11 a02 a12 x y -
      complexBilinearVerticalStrip a00 a10 a01 a11 a02 a12 x y') <=
        D * |y - y'| := by
  by_cases hy : y <= 1
  · by_cases hy' : y' <= 1
    · have h := complexBilinearCell_norm_sub_le
        a00 a10 a01 a11 x x y y' D hx0 hx1 hy0 hy
        h00_10 h01_11 h00_01 h10_11
      simpa [complexBilinearVerticalStrip, hy, hy'] using h
    · have hy'1 : 1 < y' := lt_of_not_ge hy'
      have h := complexBilinearCell_verticalAdjacent_norm_sub_le
        a00 a10 a01 a11 a02 a12 x x y (y' - 1) D
        hx0 hx1 hx0 hx1 hy0 hy (by linarith) (by linarith)
        h00_10 h01_11 h00_01 h10_11 h02_12 h01_02 h11_12
      simpa [complexBilinearVerticalStrip, hy, hy',
        abs_of_nonpos (by linarith : y - y' <= 0)] using h
  · have hy1 : 1 < y := lt_of_not_ge hy
    by_cases hy' : y' <= 1
    · have h := complexBilinearCell_verticalAdjacent_norm_sub_le
        a00 a10 a01 a11 a02 a12 x x y' (y - 1) D
        hx0 hx1 hx0 hx1 hy0' hy' (by linarith) (by linarith)
        h00_10 h01_11 h00_01 h10_11 h02_12 h01_02 h11_12
      rw [norm_sub_rev]
      simpa [complexBilinearVerticalStrip, hy, hy',
        abs_of_nonneg (by linarith : 0 <= y - y')] using h
    · have hy'1 : 1 < y' := lt_of_not_ge hy'
      have h := complexBilinearCell_norm_sub_le
        a01 a11 a02 a12 x x (y - 1) (y' - 1) D hx0 hx1
        (by linarith) (by linarith) h01_11 h02_12 h01_02 h11_12
      simpa [complexBilinearVerticalStrip, hy, hy'] using h


end
end StatMech.Universality
