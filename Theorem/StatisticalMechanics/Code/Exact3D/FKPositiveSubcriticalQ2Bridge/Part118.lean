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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part120
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem freeQ2BoundaryVertexDirectionalRate_of_convexSurfaceTensionUpper
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
    FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical := by
  intro β hβpos hβc
  rcases htension β hβpos hβc with
    ⟨C, k, tension, boundaryCoord, hC, hconv, hflip, hhom, hface, hpoint,
      hxAxisRate⟩
  refine
    ⟨C, tension surfaceXAxisUnit, k,
      fun n v => tension (boundaryCoord n v), hC, ?_, hpoint,
      hxAxisRate⟩
  filter_upwards [hface] with n hface_n
  intro v hv
  rcases hface_n v hv with ⟨a, b, hcoord⟩
  rw [hcoord]
  simpa [mul_comm] using
    surfaceTension_cubeFace_xAxisRate_le_of_convex_flip23_hom
      hconv hflip hhom (by positivity : 0 ≤ (n : ℝ))


theorem
    freeQ2BoundaryVertexDirectionalRate_of_actualConvexSurfaceTensionUpper
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
    FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical := by
  intro β hβpos hβc
  rcases htension β hβpos hβc with
    ⟨C, k, tension, hC, hconv, hflip1, hflip2, hflip3, hswap12, hswap13,
      hhom, hpoint, hxAxisRate⟩
  refine
    ⟨C, tension surfaceXAxisUnit, k,
      fun n v => tension (surfaceVecOfBoxVertex n v), hC, ?_, hpoint,
      hxAxisRate⟩
  filter_upwards [eventually_ge_atTop (0 : ℕ)] with n _hn
  intro v hv
  simpa [surfaceVecOfBoxVertex, mul_comm] using
    surfaceTension_cubeBoundary_xAxisRate_le_of_convex_signedPerm_hom
      hconv hflip1 hflip2 hflip3 hswap12 hswap13 hhom
      (by positivity : 0 ≤ (n : ℝ))
      (boxBoundary3_surfaceVec_face_cases n v hv)


theorem
    freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_directionalRate
    (hdir :
      FreeQ2BoundaryVertexPolynomialDirectionalRatePositiveSubcritical) :
    FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical := by
  intro β hβpos hβc
  rcases hdir β hβpos hβc with
    ⟨C, xRate, k, boundaryRate, hC, hrateLower, hpoint, hxAxisRate⟩
  refine ⟨C, xRate, k, hC, ?_, hxAxisRate⟩
  filter_upwards [hrateLower, hpoint] with n hrateLower_n hpoint_n
  intro v hv
  have hexp_le :
      Real.exp (-(boundaryRate n v)) ≤
        Real.exp (-(xRate * (n : ℝ))) := by
    exact Real.exp_le_exp.mpr (by linarith [hrateLower_n v hv])
  have hpref_nonneg : 0 ≤ C * (n : ℝ) ^ k := by positivity
  calc
    ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
        ≤ C * (n : ℝ) ^ k * Real.exp (-(boundaryRate n v)) :=
      hpoint_n v hv
    _ ≤ C * (n : ℝ) ^ k * Real.exp (-(xRate * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hexp_le hpref_nonneg


theorem
    freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_convexSurfaceTensionUpper
    (htension :
      FreeQ2BoundaryVertexConvexSurfaceTensionUpperPositiveSubcritical) :
    FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical :=
  freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_directionalRate
    (freeQ2BoundaryVertexDirectionalRate_of_convexSurfaceTensionUpper
      htension)


theorem
    freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_actualConvexSurfaceTensionUpper
    (htension :
      FreeQ2BoundaryVertexActualConvexSurfaceTensionUpperPositiveSubcritical) :
    FreeQ2BoundaryVertexPolynomialRateWithXAxisLogRatePositiveSubcritical :=
  freeQ2BoundaryVertexPolynomialRateWithXAxisLogRate_of_directionalRate
    (freeQ2BoundaryVertexDirectionalRate_of_actualConvexSurfaceTensionUpper
      htension)


end Exact3D
end StatMech
