/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedHadamardPrereq
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanRootControl.Part2
public import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
public import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
public import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part2
open scoped BigOperators


namespace StatMech.FrontierA

public noncomputable section

structure EvenHadamardFactorization (F : Complex → Complex) where
  roots : Nat → Real
  roots_nonneg : ∀ n, 0 ≤ roots n
  roots_summable : Summable roots
  value_zero_ne : F 0 ≠ 0
  normalized_eq : ∀ z,
    F z / F 0 = hadamardRootProduct roots z


end
end StatMech.FrontierA
