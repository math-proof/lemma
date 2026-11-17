/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/EllipticParametrix.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Geometry.Manifold.Instances.Real
public import Structure.v1.Atlas.GeometryOfManifolds.code.EllipticParametrix

@[expose] public section

open ContinuousLinearMap Finset Manifold


/-- The principal symbol $\sigma(L)(\xi)$ of an elliptic operator $L$, evaluated at cotangent
direction $\xi$. -/
noncomputable def IsEllipticOperator.symbol
    {n : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : E →L[ℝ] F}
    (hL : IsEllipticOperator n L) (ξ : Fin n → ℝ) : E →L[ℝ] F :=
  principalSymbol (k := hL.order) hL.coeff ξ


