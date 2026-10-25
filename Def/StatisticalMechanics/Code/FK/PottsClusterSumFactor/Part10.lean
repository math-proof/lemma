/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Instance.StatisticalMechanics.Code.FK.PottsClusterSumFactor
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


noncomputable def pottsClusterSumJointMeasure
    {d q : Nat} [NeZero q] (boundaryColor : Fin q)
    (edgeMeasure : Measure (ConfigSpace (Sym2 (Site d)))) :
    Measure ((Site d -> Fin q) × ConfigSpace (Sym2 (Site d))) :=
  Measure.map (pottsClusterSumJointFactor boundaryColor)
    (edgeMeasure.prod (pottsIIDLabelMeasure d q))


end StatMech.FK
