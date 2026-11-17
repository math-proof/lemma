/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralCriticalDivergence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.Universality.HexCoefficientAggregation.Part2
public import Theorem.StatisticalMechanics.Code.Universality.HexInjections.Part7
public import Theorem.StatisticalMechanics.Code.Universality.HexBridgeRecon.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexColumnMembershipClose.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part5
public import Theorem.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary.Part3
public import Theorem.StatisticalMechanics.Code.Universality.HexLiteralCriticalDivergence.Part2


public section

namespace StatMech.Universality

open HexWalk

open scoped BigOperators


structure HexLiteralSideFibers (a : ℂ) (h0 : ℤ) where
  
  Index : ℕ → Type*
  
  turns : ∀ T, Index T → List ℤ
  
  turns_injective : ∀ T, Function.Injective (turns T)
  
  height : ∀ T, Index T → ℕ

end StatMech.Universality
