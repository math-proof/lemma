/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumFactor
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


def pottsLabelTwist {ι : Type*} [DecidableEq ι] {q : Nat} [NeZero q]
    (root : ι) (increment : Fin q) (label : ι -> Fin q) : ι -> Fin q :=
  Function.update label root (label root + increment)


end StatMech.FK
