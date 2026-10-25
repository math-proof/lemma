/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Def.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part7
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


theorem measurableSet_pottsLabelSumEvent {d q : Nat} [NeZero q]
    (F : Finset (Site d)) (a : Fin q) :
    MeasurableSet (pottsLabelSumEvent F a) := by
  unfold pottsLabelSumEvent cylinder
  apply MeasurableSet.preimage
  · exact Set.toFinite {label : F -> Fin q | ∑ x, label x = a} |>.measurableSet
  · exact measurable_pi_lambda _ fun x => measurable_pi_apply x.1


end StatMech.FK
