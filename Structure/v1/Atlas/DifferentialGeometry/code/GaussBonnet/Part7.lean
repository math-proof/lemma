/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussBonnet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Cast.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Def.v1.Atlas.DifferentialGeometry.code.GaussMapDegree.Part4
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.GaussMapDegree
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
public import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
public import Def.v1.Atlas.DifferentialGeometry.code.GaussBonnet.Part6
public section

open Finset Real


namespace GaussBonnetBoundary

open Real MeasureTheory

variable (D : DiscRegion)

structure GeodesicTriangleRegion extends DiscRegion where
  corners_eq : toDiscRegion.numCorners = 3
  angle₁ : ℝ
  angle₂ : ℝ
  angle₃ : ℝ
  geodesic_boundary : toDiscRegion.totalGeodesicCurvature = 0
  ext_angle_0 : toDiscRegion.exteriorAngles (Fin.cast corners_eq.symm 0) = π - angle₁
  ext_angle_1 : toDiscRegion.exteriorAngles (Fin.cast corners_eq.symm 1) = π - angle₂
  ext_angle_2 : toDiscRegion.exteriorAngles (Fin.cast corners_eq.symm 2) = π - angle₃

end GaussBonnetBoundary
