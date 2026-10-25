/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ChernClassProperties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.GeometryOfManifolds.code.CompatibleComplexStructures
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.CompatibleComplexStructures
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ConnectionsCurvature
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.ConnectionsCurvature.Part7
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.LinearAlgebra.Orientation
import Structure.v1.Atlas.GeometryOfManifolds.code.ChernClassProperties
set_option autoImplicit false

open SymplecticLinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℝ V]


/-- The Chern–Weil map applied to a curvature-like matrix $A$, producing the corresponding
characteristic form via `embed` and `extract`. -/
def ComplexVectorBundleData.chernWeilMapDef
    {intCoh : IsIntegralCohomologyClass Ω d}
    (bundle : ComplexVectorBundleData I M F E Ω d d_squared intCoh r totalAlg)
    (A : Matrix (Fin r) (Fin r) (Ω 2)) : Ω (2 * r - 1 + 1) :=
  bundle.extract (totalChernForm (A.map bundle.embed) bundle.chernWeilParam)

/-- The top Chern form representative $c_r(E, \nabla)$ obtained from the bundle's curvature
matrix via Chern–Weil. -/
def ComplexVectorBundleData.topChernRep
    {intCoh : IsIntegralCohomologyClass Ω d}
    (bundle : ComplexVectorBundleData I M F E Ω d d_squared intCoh r totalAlg) :
    Ω (2 * r - 1 + 1) :=
  bundle.chernWeilMapDef bundle.curvatureMatrix

