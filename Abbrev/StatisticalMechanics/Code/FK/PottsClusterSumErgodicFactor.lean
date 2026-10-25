/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsClusterSumErgodicFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumFactor.Part10
import Theorem.StatisticalMechanics.Code.FK.PottsClusterSumErgodicFactor
open MeasureTheory Set


namespace StatMech.FK

abbrev pottsSpinShift {d q : Nat} (g : Multiplicative (Lattice.Site d))
    (spin : Lattice.Site d -> Fin q) : Lattice.Site d -> Fin q :=
  pottsLabelShift g spin


end StatMech.FK
