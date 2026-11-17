/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Distribution.Support
public import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzPartition
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzPartition
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzCutoffConvergence
public import Def.v1.Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence

public section

noncomputable section

open scoped SchwartzMap

open Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℝ E]

namespace SchwartzMap

end SchwartzMap
end
