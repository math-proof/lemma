/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.Strip.Part2
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossing.Part2
open Set MeasureTheory
open scoped ENNReal NNReal


namespace StatMech

namespace RSW

namespace BoxCrossing

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


def rectangleCrossingEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  horizontalCrossingEvent 0 (2 * n) 0 n


def rectLeftHalfEvent (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n) (hzc : 0 ≤ z 1)
    (hzd : z 1 ≤ n) : Set (ConfigSpace (Sym2 (Site 2))) :=
  leftHalfCrossingEvent 0 n 0 n z
    (rightSide_subset (mem_shared_column (a := 0) (m := n) (b := 2 * n) (c := 0) (d := n)
      hn (by linarith) hz0 hzc hzd).1)


def rectRightHalfEvent (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n) (hzc : 0 ≤ z 1)
    (hzd : z 1 ≤ n) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rightHalfCrossingEvent n (2 * n) 0 n z
    (leftSide_subset (mem_shared_column (a := 0) (m := n) (b := 2 * n) (c := 0) (d := n)
      hn (by linarith) hz0 hzc hzd).2)


end BoxCrossing
end RSW
end StatMech
