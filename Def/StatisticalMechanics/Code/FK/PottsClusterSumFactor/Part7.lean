/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part6
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


def pottsLabelSumEvent {d q : Nat} [NeZero q]
    (F : Finset (Site d)) (a : Fin q) :
    Set (Site d -> Fin q) :=
  cylinder (α := fun _ : Site d => Fin q) F
    {label | ∑ x, label x = a}

end StatMech.FK
