/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter2/UnbalancingLights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter2.UnbalancingLights
open Finset BigOperators

public section

namespace UnbalancingLights

/-- The sign flip operation is its own inverse. -/
lemma signFlip_involutive {n : ℕ} (a : Fin n → ℤ) :
    Function.Involutive (signFlip a) := by
  intro y; ext j; simp [signFlip]

end UnbalancingLights
