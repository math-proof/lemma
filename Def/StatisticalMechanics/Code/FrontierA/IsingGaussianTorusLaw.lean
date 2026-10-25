/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianTorusLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusLaplacianNormalization.Part4
import Theorem.StatisticalMechanics.Code.FK.HolleyCoupling.Part2
open Finset MeasureTheory
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech Ising

noncomputable section

variable {d k : Nat}


def isingTorusZeroFieldMass (beta : Real)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) : Real :=
  Real.exp (-(beta / 2) *
      isingTorusDirichlet (isingTorusSpinField sigma)) /
    isingTorusShiftedPartition (d := d) (k := k) beta 0

end
end StatMech.FrontierA
