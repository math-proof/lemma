/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/DistributionSupport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.Support
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzPartition
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzPartition
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzCutoffConvergence
import Def.v1.Atlas.DifferentialAnalysis.code.SchwartzCutoffConvergence


noncomputable section

open scoped SchwartzMap

open Distribution

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℝ E]

namespace SchwartzMap

end SchwartzMap
end
