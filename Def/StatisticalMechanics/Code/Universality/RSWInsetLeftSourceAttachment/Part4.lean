/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetLeftSourceAttachment.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetSourceAttachment.Part2
import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part2
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_insetLeftSourceCoreEvent (n : Int) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rlc_lrRestrictedEvent (-2 * n) (-1) (-n) n rlc_lowerHalf rlc_strictUpperHalf

end
end StatMech.Universality
