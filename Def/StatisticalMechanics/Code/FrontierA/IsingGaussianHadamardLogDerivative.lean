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
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

def hadamardRootFactor (roots : Nat → Real) (n : Nat) (z : Complex) : Complex :=
  1 + (roots n : Complex) * z ^ 2


def hadamardRootProduct (roots : Nat → Real) (z : Complex) : Complex :=
  ∏' n, hadamardRootFactor roots n z

end
end StatMech.FrontierA
