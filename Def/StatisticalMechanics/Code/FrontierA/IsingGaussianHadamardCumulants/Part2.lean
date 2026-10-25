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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardCumulants
open Filter
open scoped BigOperators Complex Nat


namespace StatMech.FrontierA

noncomputable section

def hadamardScalarCumulant (F : Complex → Complex) (order : Nat) : Real :=
  if order = 0 then 0
  else (iteratedDeriv (order - 1) (logDeriv F) 0).re


end
end StatMech.FrontierA
