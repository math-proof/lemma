/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfProbability/code/FubiniTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.MeasureTheory.Integral.Prod
open MeasureTheory MeasurableSpace Measure ENNReal


noncomputable section

variable {α β : Type*}

variable [MeasurableSpace α] [MeasurableSpace β]

variable {μ : Measure α} {ν : Measure β}

variable [SFinite μ] [SFinite ν]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

end
