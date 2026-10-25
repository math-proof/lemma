/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumePhaseTransport.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolume.Part8
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokalWiredCorrelation.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.PcUpperAllDimensions
import Mathlib.MeasureTheory.Measure.Portmanteau
open MeasureTheory Filter Topology
open scoped BigOperators ENNReal


namespace StatMech.FK

open Lattice Percolation IsingFK

noncomputable section

def pottsColorEvent (d q : Nat) (x : Site d) (b : Fin q) :
    Set (PottsConfig d q) :=
  {sigma | sigma x = b}

end
end StatMech.FK
