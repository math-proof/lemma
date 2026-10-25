/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumeTwoPoint.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolumePhaseTransport.Part2
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokalFull.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.FreeInfiniteMultipointES
open MeasureTheory Filter Topology


namespace StatMech.FK

open Lattice Percolation

noncomputable section

def pottsAgreementEvent (d q : Nat) (x y : Site d) :
    Set (PottsConfig d q) :=
  {sigma | sigma x = sigma y}

end
end StatMech.FK
