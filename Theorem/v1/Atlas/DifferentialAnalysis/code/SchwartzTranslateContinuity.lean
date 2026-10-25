/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzTranslateContinuity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.SchwartzTranslation
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzTranslation
open scoped SchwartzMap Topology
open Metric Filter


noncomputable section

namespace SchwartzMap

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end SchwartzMap
end
