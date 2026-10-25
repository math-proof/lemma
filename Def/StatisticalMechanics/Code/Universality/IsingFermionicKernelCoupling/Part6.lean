/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part4


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def isingLeapfrogEncodeStep (d : Int × Int) : Bool × Bool :=
  (decide (d.1 = 1), decide (d.2 = 1))

def isingLeapfrogEncodeSteps (path : List (Int × Int)) :
    List (Bool × Bool) :=
  path.map isingLeapfrogEncodeStep

end
end StatMech.Universality
