/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part13


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


def finiteCRSFCycleSupportSelection (next : V -> V) : Type _ :=
  Set.range
    (fun X : finiteCRSFWitnessFiber next => X.1.1.support)


noncomputable def finiteCRSFWitnessFiberEquivCycleSupport
    (next : V -> V) :
    finiteCRSFWitnessFiber next ≃ finiteCRSFCycleSupportSelection next :=
  Equiv.ofInjective
    (fun X : finiteCRSFWitnessFiber next => X.1.1.support)
    (finiteCRSFWitnessFiber_support_injective next)


end StatMech.FrontierA
