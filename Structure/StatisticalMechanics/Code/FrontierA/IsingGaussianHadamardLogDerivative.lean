/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardLogDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianWeightedHadamardPrereq
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianNewmanRootControl.Part2
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part2
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

structure EvenHadamardFactorization (F : Complex → Complex) where
  roots : Nat → Real
  roots_nonneg : ∀ n, 0 ≤ roots n
  roots_summable : Summable roots
  value_zero_ne : F 0 ≠ 0
  normalized_eq : ∀ z,
    F z / F 0 = hadamardRootProduct roots z


end
end StatMech.FrontierA
