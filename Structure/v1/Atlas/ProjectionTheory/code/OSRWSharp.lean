/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/OSRWSharp.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.DeltaRegular
open Metric Set InnerProductSpace


namespace ProjectionTheory

/-- A `δ`-tube in $\mathbb{R}^2$, recorded by its midpoint, its direction angle, and its
width (intended to be the small parameter `δ`). The tube is a thin rectangle of length
roughly `1` and width `width`. -/
structure DeltaTube where
  midpoint : EuclideanSpace ℝ (Fin 2)
  direction : ℝ
  width : ℝ

end ProjectionTheory
