/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.IsingFK.Coloring.Part6
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part4
open MeasureTheory Set


namespace StatMech.FK

open Lattice Percolation


noncomputable def pottsClusterSumJointFactor {d q : Nat} [NeZero q]
    (boundaryColor : Fin q)
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :
    (Site d -> Fin q) × ConfigSpace (Sym2 (Site d)) :=
  (pottsClusterSumSpin boundaryColor input.1 input.2, input.1)


noncomputable def pottsClusterFactorInputShift {d q : Nat}
    (g : Multiplicative (Site d))
    (input : ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q)) :
    ConfigSpace (Sym2 (Site d)) × (Site d -> Fin q) :=
  (ConfigSpace.shift g input.1, pottsLabelShift g input.2)


noncomputable def pottsJointShift {d q : Nat} (g : Multiplicative (Site d))
    (joint : (Site d -> Fin q) × ConfigSpace (Sym2 (Site d))) :
    (Site d -> Fin q) × ConfigSpace (Sym2 (Site d)) :=
  (pottsLabelShift g joint.1, ConfigSpace.shift g joint.2)


end StatMech.FK
