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
import Def.v1.Atlas.GeometryOfManifolds.code.EllipticParametrix
open ContinuousLinearMap Finset Manifold


/-- An elliptic linear differential operator $L: \Gamma(E) \to \Gamma(F)$ of order $k$:
locally $L = \sum_{|\alpha| \le k} A_\alpha \partial^\alpha$, with bijective principal symbol
$\sigma_k(L)(\xi)$ for all $\xi \ne 0$. -/
structure IsEllipticOperator
    (n : ℕ)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) where
  order : ℕ
  coeff : MultiIndex n → (E →L[ℝ] F)
  coeff_support : ∀ (α : MultiIndex n), multiIndexDegree α > order → coeff α = 0
  partialDeriv : MultiIndex n → (E →L[ℝ] E)
  local_expression : ∀ (s : E),
    L s = ∑ α ∈ multiIndicesOfDegreeLE n order, coeff α (partialDeriv α s)
  elliptic : ∀ (ξ : Fin n → ℝ), ξ ≠ 0 →
    Function.Bijective (principalSymbol (k := order) coeff ξ)

