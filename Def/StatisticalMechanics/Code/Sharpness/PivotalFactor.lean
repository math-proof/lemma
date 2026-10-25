/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Russo


namespace StatMech

namespace Sharpness

open ConfigSpace Function Finset StatMech

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def openInd (ω : ConfigSpace E) (e : E) : ℝ := if ω e then 1 else 0

end Sharpness
end StatMech
