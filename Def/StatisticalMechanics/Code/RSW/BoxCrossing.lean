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
import Theorem.StatisticalMechanics.Code.RSW.BoxCrossing
open Set MeasureTheory
open scoped ENNReal NNReal


namespace StatMech

namespace RSW

namespace BoxCrossing

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


def squareCrossingEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  horizontalCrossingEvent 0 n 0 n


def squareDualCrossingEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  dualVerticalCrossingEvent 0 n 0 n


end BoxCrossing
end RSW
end StatMech
