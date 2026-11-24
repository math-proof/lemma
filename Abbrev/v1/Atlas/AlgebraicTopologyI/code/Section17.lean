module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section16
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.ZMod.QuotientGroup


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- The unit $n$-sphere $S^n \subset \mathbb{R}^{n+1}$, defined as the metric sphere of
radius $1$ in $\mathbb{R}^{n+1}$. -/
abbrev Sphere (n : ℕ) : Type :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

end RealProjectiveSpace
end
