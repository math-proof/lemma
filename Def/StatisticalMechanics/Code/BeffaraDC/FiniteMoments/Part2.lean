/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/FiniteMoments.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.RussoHamming.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.FiniteMoments.Part2


namespace StatMech

namespace BeffaraDC

open ConfigSpace Function Finset

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def expHammingMoment (p : ℝ) (A : Set (ConfigSpace E)) (t : ℝ) : ℝ :=
  expect p (fun ω => Real.exp (t * (hammingToSet A ω : ℝ)))


end BeffaraDC
end StatMech
