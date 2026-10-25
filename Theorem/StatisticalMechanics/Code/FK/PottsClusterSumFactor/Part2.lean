/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Def.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part2
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


theorem sum_pottsLabelTwist {ι : Type*} [Fintype ι] [DecidableEq ι]
    {q : Nat} [NeZero q] (root : ι) (increment : Fin q)
    (label : ι -> Fin q) :
    ∑ i, pottsLabelTwist root increment label i =
      (∑ i, label i) + increment := by
  rw [pottsLabelTwist, Finset.sum_update_of_mem (Finset.mem_univ root)]
  simp
  abel


end StatMech.FK
