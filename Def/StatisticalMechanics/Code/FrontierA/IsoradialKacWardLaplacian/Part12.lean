/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part10


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


namespace finiteCRSFCycleSupport

noncomputable def equivAtomicCycles (next : V -> V) :
    finiteCRSFCycleSupport next ≃ Finset (finiteCRSFAtomicCycle next) where
  toFun := toAtomicCycles
  invFun := ofAtomicCycles
  left_inv := ofAtomicCycles_toAtomicCycles
  right_inv := toAtomicCycles_ofAtomicCycles


noncomputable def atomicCycleHolonomy {next : V -> V}
    (transport : V -> V -> Complex) (S : finiteCRSFCycleSupport next)
    (cycle : Equiv.Perm (↑S.carrier)) : Complex :=
  ∏ v ∈ cycle.support, transport v (next v)

end finiteCRSFCycleSupport
end StatMech.FrontierA
