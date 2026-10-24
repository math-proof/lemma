/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/FourierAnalysis/code/FourierOrthonormalBasis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

noncomputable section

open MeasureTheory MeasureTheory.Measure AddCircle

namespace FourierOrthonormalBasis

variable {T : ℝ} [hT : Fact (0 < T)]
