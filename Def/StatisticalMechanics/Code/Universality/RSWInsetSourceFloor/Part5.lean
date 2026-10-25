/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWInsetSourceFloor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWInsetLeftSourceAttachment.Part3
import Theorem.StatisticalMechanics.Code.Universality.RSWInsetSourceFloor.Part4
open Finset SimpleGraph Set MeasureTheory


namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section

def rlc_insetRightOddToUpper (n : Int) :=
  rlc_lrRestrictedEvent 1 (2 * n) (-n) (n - 1) Set.univ rlc_upperHalf

def rlc_insetRightOddToStrictLower (n : Int) :=
  rlc_lrRestrictedEvent 1 (2 * n) (-n) (n - 1) Set.univ rlc_strictLowerHalf

def rlc_insetRightOddStrictLowerToRight (n : Int) :=
  rlc_lrRestrictedEvent 1 (2 * n) (-n) (n - 1) rlc_strictLowerHalf Set.univ

def rlc_insetRightOddUpperToRight (n : Int) :=
  rlc_lrRestrictedEvent 1 (2 * n) (-n) (n - 1) rlc_upperHalf Set.univ

def rlc_insetRightOddSourceCoreEvent (n : Int) :=
  rlc_lrRestrictedEvent 1 (2 * n) (-n) (n - 1)
    rlc_strictLowerHalf rlc_upperHalf

end
end StatMech.Universality
