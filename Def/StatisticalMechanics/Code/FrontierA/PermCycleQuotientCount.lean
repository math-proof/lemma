/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/PermCycleQuotientCount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialRibbonBoundaryParity.Part3
import Abbrev.StatisticalMechanics.Code.FrontierA.PermCycleQuotientCount


namespace StatMech.FrontierA

open Equiv

variable {D : Type*} [Fintype D] [DecidableEq D]


noncomputable def permCycleRepresentativeOf (sigma : Perm D) (x : D) :
    PermCycleRepresentative sigma := by
  classical
  exact if hx : x ∈ sigma.support then
    Sum.inl ⟨sigma.cycleOf x,
      Equiv.Perm.cycleOf_mem_cycleFactorsFinset_iff.mpr hx⟩
  else
    Sum.inr ⟨x, by simpa only [Equiv.Perm.notMem_support] using hx⟩

end StatMech.FrontierA
