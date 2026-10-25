/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/RealAnalysis/code/Integration/Basic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic


namespace Integration

/-- The set `C([a,b])` of continuous real-valued functions on the closed interval `[a,b]`. -/
def C_ab (a b : ℝ) : Set (ℝ → ℝ) :=
  {f : ℝ → ℝ | ContinuousOn f (Set.Icc a b)}

end Integration
