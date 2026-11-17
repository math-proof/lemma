/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Def.v1.Atlas.DifferentialAnalysis.code.SchwartzSeminorms
public import Theorem.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzSeminorms
open scoped SchwartzMap

public section

noncomputable section

namespace TemperedDistributions

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end TemperedDistributions
end
