/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticParametrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Structure.v1.Atlas.GeometryOfManifolds.code.EllipticParametrix.Part2
open ContinuousLinearMap Finset Manifold


/-- Pointwise principal symbol $\sigma_k(L)(x, \xi) = \sum_{|\alpha| = k} \xi^\alpha A_\alpha(x)$
of an operator on a manifold $M$ at point $x$ and cotangent vector $\xi$. -/
noncomputable def principalSymbolAt {n : ℕ} {k : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {M : Type*}
    (A : M → MultiIndex n → (E →L[ℝ] F)) (x : M) (ξ : Fin n → ℝ) : E →L[ℝ] F :=
  ∑ α ∈ multiIndicesOfDegree n k, (multiIndexMonomial α ξ) • (A x α)


