/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part5
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


def pottsClusterEqEvent (d : Nat) (x : Site d) (F : Finset (Site d)) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  {omega | cluster d omega x = (F : Set (Site d))}

end StatMech.FK
