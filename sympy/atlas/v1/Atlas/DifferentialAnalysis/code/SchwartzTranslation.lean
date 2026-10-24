/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzTranslation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SchwartzSeminorms
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SchwartzSeminorms

open scoped SchwartzMap

noncomputable section

namespace TemperedDistributions

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
