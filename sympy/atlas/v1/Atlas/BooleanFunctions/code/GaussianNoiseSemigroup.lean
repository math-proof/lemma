/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GaussianNoiseSemigroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.BooleanFunctions.code.OUSemigroup
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.OUSemigroup
import sympy.atlas.v1.Atlas.BooleanFunctions.code.GaussianStability

set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace GaussianStability

variable {n : ℕ}
