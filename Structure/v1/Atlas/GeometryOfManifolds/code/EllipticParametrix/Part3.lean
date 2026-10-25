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
import Def.v1.Atlas.GeometryOfManifolds.code.EllipticParametrix.Part3
open ContinuousLinearMap Finset Manifold


/-- An elliptic linear differential operator $L: \Gamma(E) \to \Gamma(F)$ on a compact manifold
$M$: pointwise of order $k$ with bijective principal symbol at every $(x, \xi)$, $\xi \ne 0$. -/
structure IsEllipticOperatorOnManifold
    (n : ℕ)
    (M : Type*) [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [CompactSpace M] [IsManifold (𝓡 n) ⊤ M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : (M → E) → (M → F)) where
  order : ℕ
  coeff : M → MultiIndex n → (E →L[ℝ] F)
  coeff_support : ∀ (x : M) (α : MultiIndex n), multiIndexDegree α > order → coeff x α = 0
  partialDeriv : MultiIndex n → (M → E) → (M → E)
  local_expression : ∀ (s : M → E) (x : M),
    L s x = ∑ α ∈ multiIndicesOfDegreeLE n order, coeff x α (partialDeriv α s x)
  elliptic : ∀ (x : M) (ξ : Fin n → ℝ), ξ ≠ 0 →
    Function.Bijective (principalSymbolAt (k := order) coeff x ξ)

