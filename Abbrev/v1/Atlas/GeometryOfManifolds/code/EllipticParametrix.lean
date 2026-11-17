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
@[expose] public section

open ContinuousLinearMap Finset Manifold


/-- A multi-index $\alpha = (\alpha_1, \ldots, \alpha_n) \in \mathbb{N}^n$ on $n$ variables. -/
abbrev MultiIndex (n : ℕ) := Fin n → ℕ

