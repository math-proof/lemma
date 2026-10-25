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
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part2
open Set


namespace StatMech

namespace RSW

namespace Box

open StatMech.Lattice

open StatMech.TwoDim


def HorizontalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Prop :=
  ∃ (x : leftSide a b c d) (y : rightSide a b c d),
    ConnectedWithin 2 ω (rect a b c d)
      ⟨(x : Site 2), leftSide_subset x.2⟩ ⟨(y : Site 2), rightSide_subset y.2⟩


def VerticalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b c d : ℤ) : Prop :=
  ∃ (x : bottomSide a b c d) (y : topSide a b c d),
    ConnectedWithin 2 ω (rect a b c d)
      ⟨(x : Site 2), bottomSide_subset x.2⟩ ⟨(y : Site 2), topSide_subset y.2⟩


def horizontalCrossingEvent (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | HorizontalCrossing ω a b c d}


def verticalCrossingEvent (a b c d : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | VerticalCrossing ω a b c d}

end Box
end RSW
end StatMech
