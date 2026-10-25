/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumProductErgodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumErgodicFactor.Part2
import Theorem.StatisticalMechanics.Code.FK.FreePairMixingFromTail.Part3
import Theorem.StatisticalMechanics.Code.FK.FreeTailTriviality
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumProductErgodicity.Part2
open Filter Function MeasureTheory MeasurableSpace Set Topology
open scoped ENNReal symmDiff


namespace StatMech.FK

open Lattice

def pottsAllClustersFiniteEvent (d : Nat) :
    Set (ConfigSpace (Sym2 (Site d))) :=
  ⋂ x : Site d,
    {omega : ConfigSpace (Sym2 (Site d)) | (cluster d omega x).Infinite}ᶜ

end StatMech.FK
