/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.UnbalancingLights
open Finset BigOperators


namespace UnbalancingLights

/-- The sign flip operation is its own inverse. -/
lemma signFlip_involutive {n : ℕ} (a : Fin n → ℤ) :
    Function.Involutive (signFlip a) := by
  intro y; ext j; simp [signFlip]

end UnbalancingLights
