/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/GaussBonnet.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.LinearCombination
import Def.v1.Atlas.DifferentialGeometry.code.GaussMapDegree.Part4
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.GaussMapDegree
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
import Def.v1.Atlas.DifferentialGeometry.code.GaussBonnet.Part6
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
