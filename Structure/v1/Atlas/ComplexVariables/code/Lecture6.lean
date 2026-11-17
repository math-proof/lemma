/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.RCLike.Real
public import Mathlib.Topology.MetricSpace.Basic


public section

namespace Lecture6

structure Circle where
  center : ℂ
  radius : ℝ
  radius_pos : 0 < radius

end Lecture6
