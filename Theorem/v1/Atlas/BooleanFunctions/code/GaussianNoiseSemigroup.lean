/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/GaussianNoiseSemigroup.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.BooleanFunctions.code.OUSemigroup
public import Theorem.Bool.Atlas.v1.BooleanFunctions.code.OUSemigroup
public import Def.v1.Atlas.BooleanFunctions.code.GaussianStability.Part2
set_option maxHeartbeats 400000

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace GaussianStability

variable {n : ℕ}

end GaussianStability
end
