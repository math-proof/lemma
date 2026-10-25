/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ParametrixOnManifold.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Geometry.Manifold.VectorBundle.SmoothSection
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Analysis.Normed.Module.Basic
set_option autoImplicit false

open scoped Manifold


namespace ParametrixOnManifold

/-- A smooth section of a vector bundle $V \to M$ over a manifold $M$, i.e. an element of
$\Gamma(V) = C^\infty(M, V)$. -/
abbrev SmoothSection
    {E_model : Type*} [NormedAddCommGroup E_model] [NormedSpace ℝ E_model]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E_model H)
    (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
    (V : M → Type*) [TopologicalSpace (Bundle.TotalSpace F V)]
    [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V]
    [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] :=
  ContMDiffSection I F ⊤ V


end ParametrixOnManifold
