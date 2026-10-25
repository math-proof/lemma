/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStoppedFaithfulSubpath.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWSequentialStoppedConditionalLaw.Part16
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow.Part2
import Abbrev.StatisticalMechanics.Code.Universality.RSWStoppedFaithfulSubpath
open Finset SimpleGraph Set


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

noncomputable instance rlc_sourceFullCrossingPairFintype (n : Int) :
    Fintype (RlcSourceFullCrossingPair n) := by
  unfold RlcSourceFullCrossingPair RlcSourceRightFullCrossing
    RlcSourceLeftFullCrossing
  infer_instance


end
end StatMech.Universality
