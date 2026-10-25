/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/Defs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part3
open Set


namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


def DualHorizontalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Prop :=
  HorizontalCrossing (dualConfig ω) a b c d


def DualVerticalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Prop :=
  VerticalCrossing (dualConfig ω) a b c d


def dualHorizontalCrossingEvent (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | DualHorizontalCrossing ω a b c d}


def dualVerticalCrossingEvent (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | DualVerticalCrossing ω a b c d}

end Box
end RSW
end StatMech
