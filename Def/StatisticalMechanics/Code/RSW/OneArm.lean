/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/OneArm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
open Real


namespace StatMech

namespace RSW

namespace OneArm

noncomputable def roa_eps (c : ℝ) : ℝ := -Real.log (1 - c) / Real.log 2


end OneArm
end RSW
end StatMech
