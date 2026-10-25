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
import Def.v1.Atlas.DifferentialGeometry.code.GaussBonnet.Part5
open Finset Real


namespace GaussBonnetBoundary

open Real MeasureTheory

structure DiscRegion where
  surface : Set (Fin 3 → ℝ)
  region : Set (Fin 3 → ℝ)
  region_subset : region ⊆ surface
  region_connected : IsPathConnected region
  numCorners : ℕ
  gaussianCurvature : (Fin 3 → ℝ) → ℝ
  patch : HypersurfacePatch 2
  paramDomain : Set (Fin 2 → ℝ)
  paramDomain_sub : paramDomain ⊆ patch.domain
  region_eq : region = patch.f '' paramDomain
  curvature_consistent : ∀ x ∈ paramDomain,
    gaussianCurvature (patch.f x) = gaussCurvature patch x
  totalGaussianCurvature : ℝ
  totalCurvature_eq : totalGaussianCurvature =
    ∫ x in paramDomain, gaussCurvature patch x *
      Real.sqrt (firstFundamentalForm patch x).det
  totalGeodesicCurvature : ℝ
  exteriorAngles : Fin numCorners → ℝ

end GaussBonnetBoundary
