/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part7
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


def pottsClusterSumFiberEvent {d q : Nat} [NeZero q]
    (boundaryColor : Fin q) (x : Site d) (a : Fin q) :
    Set (ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :=
  (if a = boundaryColor then
      Prod.fst ⁻¹'
        {omega : ConfigSpace (Sym2 (Site d)) |
          (cluster d omega x).Infinite}
    else ∅) ∪
    ⋃ F : Finset (Site d),
      Prod.fst ⁻¹' pottsClusterEqEvent d x F ∩
        Prod.snd ⁻¹' pottsLabelSumEvent F a

end StatMech.FK
