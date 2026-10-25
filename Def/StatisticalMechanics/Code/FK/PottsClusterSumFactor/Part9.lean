/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part8
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


noncomputable def pottsIIDLabelMeasure (d q : Nat) [NeZero q] :
    Measure (Site d -> Fin q) :=
  Measure.infinitePi fun _ : Site d =>
    (PMF.uniformOfFintype (Fin q)).toMeasure


end StatMech.FK
