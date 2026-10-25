/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Instance.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part4


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


theorem finiteCRSFAtomicCycle_support_disjoint {next : V -> V}
    {cycle cycle' : finiteCRSFAtomicCycle next} (hne : cycle ≠ cycle') :
    Disjoint cycle.1.support cycle'.1.support := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  apply hne
  apply Subtype.ext
  apply cycle.2.1.eq_on_support_inter_nonempty_congr cycle'.2.1
  · intro w hw
    have hw' := Finset.mem_inter.mp hw
    exact (cycle.2.2 w hw'.1).trans (cycle'.2.2 w hw'.2).symm
  · exact (cycle.2.2 v hv).trans (cycle'.2.2 v hv').symm
  · exact hv


end StatMech.FrontierA
