/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/PermCycleQuotientCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity.Part3


namespace StatMech.FrontierA

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]


abbrev PermCycleClass (sigma : Perm D) :=
  Quot (Equiv.Perm.SameCycle.setoid sigma)


abbrev PermCycleRepresentative (sigma : Perm D) :=
  sigma.cycleFactorsFinset ⊕ Function.fixedPoints sigma

end StatMech.FrontierA
