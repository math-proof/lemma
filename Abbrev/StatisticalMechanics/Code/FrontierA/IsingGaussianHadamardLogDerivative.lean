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
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative.Part3
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

section FiniteIsing

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


abbrev FiniteIsingWeightedHadamardFactorization
    (beta : Real) (a : V → Real) : Type :=
  EvenHadamardFactorization (finiteIsingWeightedFieldPartition G beta a)

end FiniteIsing
end
end StatMech.FrontierA
