/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CotangentBundleBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.ManifoldDFS.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ManifoldDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff
open DifferentialFormSpace


/-- The cotangent bundle $T^*M$ as the disjoint union $\bigsqcup_{x \in M} T^*_x M$ of cotangent spaces. -/
def CotangentBundle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Type _ :=
  Σ (x : M), (TangentSpace I x →ₗ[ℝ] ℝ)

namespace CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {H : Type*} [TopologicalSpace H]

variable (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]

variable [ChartedSpace H M]

/-- The bundle projection $\pi : T^*M \to M$, $(x, \xi) \mapsto x$. -/
def proj (p : CotangentBundle I M) : M := p.1

/-- Builds a cotangent vector at $x \in M$ from a covector $\xi \in T^*_x M$. -/
def mk (x : M) (ξ : TangentSpace I x →ₗ[ℝ] ℝ) : CotangentBundle I M := ⟨x, ξ⟩

end CotangentBundle
