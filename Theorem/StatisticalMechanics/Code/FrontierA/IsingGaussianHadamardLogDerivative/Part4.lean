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
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingGaussianHadamardLogDerivative
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

section FiniteIsing

open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


theorem finiteIsingWeightedFieldPartition_logDeriv_eq_tsum
    (beta : Real) (a : V → Real)
    (hF : FiniteIsingWeightedHadamardFactorization (G := G) beta a)
    {z : Complex} (hz : z ∈ hadamardRootNeighborhood hF.roots) :
    logDeriv (finiteIsingWeightedFieldPartition G beta a) z =
      ∑' n, 2 * (hF.roots n : Complex) * z /
        (1 + (hF.roots n : Complex) * z ^ 2) :=
  hF.logDeriv_eq_tsum hz

end FiniteIsing
end
end StatMech.FrontierA
