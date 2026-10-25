/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part116
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBound_of_profileDoubleScale
    (hprofile :
      FreeQ2BoundaryProfileDoubleScaleComparisonToXAxisPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBoundPositiveSubcritical := by
  intro β hβpos hβc
  refine ⟨26, 2, by norm_num, ?_⟩
  filter_upwards
      [hprofile β hβpos hβc, boxBoundaryCard3_eventually_le_26_mul_sq,
        eventually_ge_atTop 1] with
    n hprofile_n hcard hn
  intro v _hvwedge
  let x := freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume β hβpos (2 * n) n
  have hx_nonneg : 0 ≤ x := by
    dsimp [x, freeFiniteVolumeXAxisConnectionOfBetaQ2InVolume]
    exact measureReal_nonneg
  calc
    freeQ2DoubledEndpointDetourProb β hβpos n v
        ≤ freeQ2BoundaryProfileOfBeta β hβpos n :=
      freeQ2DoubledEndpointDetourProb_le_profile β hβpos n v hn
    _ ≤ ((Finset.univ.filter (FK.boxBoundary 3 n)).card : ℝ) * x := by
      simpa [x] using hprofile_n
    _ ≤ (26 * (n : ℝ) ^ 2) * x :=
      mul_le_mul_of_nonneg_right hcard hx_nonneg
    _ = 26 * (n : ℝ) ^ 2 * x := by
      ring

set_option linter.style.longLine false in


theorem
    freeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeAdditiveStrictDescentPolynomialError_of_fullStrictDescent_detourPolynomialBound
    (hfull :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeFullStrictDescentPositiveSubcritical)
    (hdetour :
      FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeDetourPolynomialBoundPositiveSubcritical) :
    FreeQ2BoundaryFreeVertexPositiveXFaceOrderedWedgeAdditiveStrictDescentPolynomialErrorPositiveSubcritical := by
  intro β hβpos hβc
  rcases hdetour β hβpos hβc with ⟨C, k, hC, hdetourHi⟩
  refine ⟨C, k, hC, ?_⟩
  filter_upwards [hfull β hβpos hβc, hdetourHi] with
    n hfull_n hdetour_n
  intro v hvwedge hheight
  rcases hfull_n v hvwedge hheight with ⟨w, hwwedge, hlt, hfull_vw⟩
  refine ⟨w, hwwedge, hlt, ?_⟩
  have hinner :=
    freeQ2DoubledInnerOriginConnProb_le_inner_add_detour_of_full
      β hβpos n v w hfull_vw
  have hdetour_w := hdetour_n w hwwedge
  linarith


end Exact3D
end StatMech
