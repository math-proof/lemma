/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/Monotonic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.FKG
import Theorem.StatisticalMechanics.Code.OSSS.Monotonic
open Finset


namespace StatMech

namespace OSSS.Monotonic

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def condNorm (μ : ConfigSpace E → ℝ) (F : Finset E) (η : ConfigSpace E) : ℝ :=
  ∑ ω, if Agree F η ω then μ ω else 0


noncomputable def condMass (μ : ConfigSpace E → ℝ) (F : Finset E) (η : ConfigSpace E) :
    ConfigSpace E → ℝ :=
  fun ω => (if Agree F η ω then μ ω else 0) / condNorm μ F η


end OSSS.Monotonic
end StatMech
