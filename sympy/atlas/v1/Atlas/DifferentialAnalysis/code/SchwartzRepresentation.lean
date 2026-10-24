/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzRepresentation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.SobolevEmbedding
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.SobolevEmbedding
import Mathlib.Analysis.Distribution.TemperateGrowth

open scoped ZeroAtInfty SchwartzMap
open MeasureTheory Filter Topology SchwartzRepresentation

noncomputable section

namespace SchwartzRepresentation

variable {n : ℕ}
