/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWStrictAxisSourcePartition
import Def.StatisticalMechanics.Code.Universality.RSWInsetSourceAttachment
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

abbrev RlcInsetRightSourcePath (n : Int) :=
  RlcRestrictedCrossingPath 1 (2 * n) (-n) n
    rlc_strictLowerHalf rlc_upperHalf


end
end StatMech.Universality
