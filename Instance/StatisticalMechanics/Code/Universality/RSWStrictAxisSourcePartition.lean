/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStrictAxisSourcePartition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWStoppedFaithfulSubpath
import Abbrev.StatisticalMechanics.Code.Universality.RSWStrictAxisSourcePartition
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable instance rlc_strictAxisFullCrossingPairFintype (n : Int) :
    Fintype (RlcStrictAxisFullCrossingPair n) := by
  unfold RlcStrictAxisFullCrossingPair RlcStrictAxisRightFullCrossing
    RlcStrictAxisLeftFullCrossing
  infer_instance


end
end StatMech.Universality
