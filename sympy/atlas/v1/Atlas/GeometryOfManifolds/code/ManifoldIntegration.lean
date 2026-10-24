/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ManifoldIntegration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.Integration
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.Integration
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ManifoldDFS
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.ManifoldDFS

set_option autoImplicit false

open DifferentialFormSpace

open scoped Manifold ContDiff


/-- A smooth manifold $M$ is compact and oriented: it carries a compact topology together with
an (abstractly recorded) orientation, the standard hypothesis under which Stokes-type integration
is defined. -/
class IsCompactOrientedManifold
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] [IsManifold I ∞ M] : Prop where
  compact : CompactSpace M
  oriented : True
