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
import Def.StatisticalMechanics.Code.Universality.IsingFermionicCenteredTensorTentRegularity


namespace StatMech.Universality

open Metric Set

open scoped unitInterval

noncomputable section

theorem complexBilinearHorizontalStrip_norm_sub_le
    (a00 a10 a20 a01 a11 a21 : Complex) (x x' y D : Real)
    (hx0 : 0 <= x) (hx2 : x <= 2)
    (hx0' : 0 <= x') (hx2' : x' <= 2)
    (hy0 : 0 <= y) (hy1 : y <= 1)
    (h00_10 : norm (a10 - a00) <= D)
    (h10_20 : norm (a20 - a10) <= D)
    (h01_11 : norm (a11 - a01) <= D)
    (h11_21 : norm (a21 - a11) <= D)
    (h00_01 : norm (a01 - a00) <= D)
    (h10_11 : norm (a11 - a10) <= D)
    (h20_21 : norm (a21 - a20) <= D) :
    norm (complexBilinearHorizontalStrip a00 a10 a20 a01 a11 a21 x y -
      complexBilinearHorizontalStrip a00 a10 a20 a01 a11 a21 x' y) <=
        D * |x - x'| := by
  by_cases hx : x <= 1
  · by_cases hx' : x' <= 1
    · have h := complexBilinearCell_norm_sub_le
        a00 a10 a01 a11 x x' y y D (by linarith) hx' hy0 hy1
        h00_10 h01_11 h00_01 h10_11
      simpa [complexBilinearHorizontalStrip, hx, hx'] using h
    · have hx'1 : 1 < x' := lt_of_not_ge hx'
      have h := complexBilinearCell_horizontalAdjacent_norm_sub_le
        a00 a10 a01 a11 a20 a21 x (x' - 1) y y D
        hx0 hx (by linarith) (by linarith) hy0 hy1 hy0 hy1
        h00_10 h01_11 h00_01 h10_11 h10_20 h11_21 h20_21
      simpa [complexBilinearHorizontalStrip, hx, hx',
        abs_of_nonpos (by linarith : x - x' <= 0)] using h
  · have hx1 : 1 < x := lt_of_not_ge hx
    by_cases hx' : x' <= 1
    · have h := complexBilinearCell_horizontalAdjacent_norm_sub_le
        a00 a10 a01 a11 a20 a21 x' (x - 1) y y D
        hx0' hx' (by linarith) (by linarith) hy0 hy1 hy0 hy1
        h00_10 h01_11 h00_01 h10_11 h10_20 h11_21 h20_21
      rw [norm_sub_rev]
      simpa [complexBilinearHorizontalStrip, hx, hx',
        abs_of_nonneg (by linarith : 0 <= x - x')] using h
    · have hx'1 : 1 < x' := lt_of_not_ge hx'
      have h := complexBilinearCell_norm_sub_le
        a10 a20 a11 a21 (x - 1) (x' - 1) y y D
        (by linarith) (by linarith) hy0 hy1
        h10_20 h11_21 h10_11 h20_21
      simpa [complexBilinearHorizontalStrip, hx, hx'] using h


end
end StatMech.Universality
