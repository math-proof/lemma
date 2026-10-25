/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicKernelCoupling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicReflectionEstimates.Part13
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicKernelCoupling.Part3


namespace StatMech.Universality

open Finset

open IsingDiagonalWalkHitSplit

noncomputable section

def isingLeapfrogChoiceStep (b : Bool × Bool) : Int × Int :=
  (if b.1 then 1 else -1, if b.2 then 1 else -1)

def isingLeapfrogChoiceSteps (bs : List (Bool × Bool)) : List (Int × Int) :=
  bs.map isingLeapfrogChoiceStep

def isingLeapfrogBoxInt {R : Nat} (p : IsingLeapfrogBox R) : Int × Int :=
  ((p.1.1 : Int), (p.2.1 : Int))

end
end StatMech.Universality
