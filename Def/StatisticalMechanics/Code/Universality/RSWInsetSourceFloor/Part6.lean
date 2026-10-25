/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWInsetSourceFloor.Part5
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_insetLeftOddToStrictUpper (n : Int) :=
  rlc_lrRestrictedEvent (-2 * n) (-1) (1 - n) n Set.univ rlc_strictUpperHalf

def rlc_insetLeftOddToLower (n : Int) :=
  rlc_lrRestrictedEvent (-2 * n) (-1) (1 - n) n Set.univ rlc_lowerHalf

def rlc_insetLeftOddLowerToRight (n : Int) :=
  rlc_lrRestrictedEvent (-2 * n) (-1) (1 - n) n rlc_lowerHalf Set.univ

def rlc_insetLeftOddStrictUpperToRight (n : Int) :=
  rlc_lrRestrictedEvent (-2 * n) (-1) (1 - n) n rlc_strictUpperHalf Set.univ

def rlc_insetLeftOddSourceCoreEvent (n : Int) :=
  rlc_lrRestrictedEvent (-2 * n) (-1) (1 - n) n
    rlc_lowerHalf rlc_strictUpperHalf

end
end StatMech.Universality
