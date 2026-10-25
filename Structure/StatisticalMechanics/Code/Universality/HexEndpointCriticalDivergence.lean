/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexEndpointCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexEndpointAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexEndpointCriticalDivergence


namespace StatMech.Universality

open HexWalk

noncomputable section

structure HexEndpointSideFibers (a : ℂ) (h0 : ℤ) where
  Index : ℕ → Type*
  turns : ∀ T, Index T → List ℤ
  turns_injective : ∀ T, Function.Injective (turns T)
  height : ∀ T, Index T → ℕ

end
end StatMech.Universality
