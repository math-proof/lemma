/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianHadamardCumulants.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianPhysicalCumulants.Part4
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
open Filter
open scoped BigOperators Complex Nat


namespace StatMech.FrontierA

noncomputable section

def hadamardRootLogTerm (r : Real) (z : Complex) : Complex :=
  2 * (r : Complex) * z / (1 + (r : Complex) * z ^ 2)

end
end StatMech.FrontierA
