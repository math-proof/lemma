/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABPhysicalDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostInfluence
import Theorem.StatisticalMechanics.Code.Sharpness.BetaReparam
import Theorem.StatisticalMechanics.Code.Sharpness.ABPhysicalDeriv
open Finset Set


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {E : Type*} [Fintype E] [DecidableEq E]


noncomputable def abpdBetaFieldParams (s : Finset E) (q : ℝ) (J : E → ℝ)
    (beta : ℝ) : E → ℝ :=
  paramOn s q (fun e => pBeta (J e) beta)


end Sharpness
end StatMech
