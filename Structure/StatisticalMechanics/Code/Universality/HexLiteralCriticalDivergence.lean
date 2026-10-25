/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexCoefficientAggregation.Part2
import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexColumnMembershipClose.Part4
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part5
import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCriticalDivergence.Part2


namespace StatMech.Universality

open HexWalk

open scoped BigOperators


structure HexLiteralSideFibers (a : ℂ) (h0 : ℤ) where
  
  Index : ℕ → Type*
  
  turns : ∀ T, Index T → List ℤ
  
  turns_injective : ∀ T, Function.Injective (turns T)
  
  height : ∀ T, Index T → ℕ

end StatMech.Universality
