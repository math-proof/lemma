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
import Structure.v1.Atlas.GeometryOfManifolds.code.EllipticParametrix.Part3
open ContinuousLinearMap Finset Manifold


/-- The principal symbol of an elliptic operator on a manifold, evaluated at $(x, \xi)$. -/
noncomputable def IsEllipticOperatorOnManifold.symbol
    {n : ℕ}
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [CompactSpace M] [IsManifold (𝓡 n) ⊤ M]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : (M → E) → (M → F)}
    (hL : IsEllipticOperatorOnManifold n M L) (x : M) (ξ : Fin n → ℝ) : E →L[ℝ] F :=
  principalSymbolAt (k := hL.order) hL.coeff x ξ

