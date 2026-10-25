/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ComplexVariables/code/Lecture6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.MetricSpace.Basic
import Def.v1.Atlas.ComplexVariables.code.Lecture6


namespace Lecture6

inductive GeneralizedCircle
  | circle : Circle → GeneralizedCircle
  | line : ℝ → ℝ → ℝ → GeneralizedCircle

end Lecture6
