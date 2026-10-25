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
import Structure.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

def EvenHadamardFactorization.scaleArgument
    {F : Complex -> Complex} (hF : EvenHadamardFactorization F)
    (c : Real) :
    EvenHadamardFactorization (fun z => F ((c : Complex) * z)) where
  roots := fun n => c ^ 2 * hF.roots n
  roots_nonneg := fun n => mul_nonneg (sq_nonneg c) (hF.roots_nonneg n)
  roots_summable := Summable.mul_left (c ^ 2) hF.roots_summable
  value_zero_ne := by simpa using hF.value_zero_ne
  normalized_eq := fun z => by
    simp only [mul_zero]
    rw [hF.normalized_eq ((c : Complex) * z)]
    unfold hadamardRootProduct hadamardRootFactor
    apply tprod_congr
    intro n
    push_cast
    ring


end
end StatMech.FrontierA
