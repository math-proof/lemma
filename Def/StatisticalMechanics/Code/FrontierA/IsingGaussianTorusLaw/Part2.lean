/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusLaplacianNormalization.Part4
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianTorusLaw
open Finset MeasureTheory
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising

noncomputable section

variable {d k : Nat}


def isingTorusZeroFieldLaw (beta : Real) :
    ProbabilityMeasure (ConfigSpace (IsingDyadicTorus d k)) :=
  ⟨FK.measOfMass (isingTorusZeroFieldMass beta),
    FK.measOfMass_isProbabilityMeasure _
      (isingTorusZeroFieldMass_nonneg beta)
      (sum_isingTorusZeroFieldMass beta)⟩

end
end StatMech.FrontierA
