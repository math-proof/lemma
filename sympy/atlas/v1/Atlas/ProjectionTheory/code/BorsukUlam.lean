/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/BorsukUlam.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

namespace BorsukUlam

/-- The unit `n`-sphere `S^n = { x ∈ ℝ^{n+1} : ‖x‖ = 1 }`, regarded as a subset of
the Euclidean space `EuclideanSpace ℝ (Fin (n + 1))`. -/
def Sphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1
