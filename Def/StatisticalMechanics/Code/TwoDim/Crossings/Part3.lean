/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Crossings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part2
open Set


namespace StatMech

namespace TwoDim

open StatMech.Lattice

variable {a b : ℤ}


def HorizontalCrossing (ω : ConfigSpace (Sym2 (Site 2))) (a b : ℤ) : Prop :=
  ∃ (x : leftSide a b) (y : rightSide a b),
    ConnectedWithin 2 ω (rectangle a b)
      ⟨(x : Site 2), leftSide_subset x.2⟩ ⟨(y : Site 2), rightSide_subset y.2⟩


def horizontalCrossingEvent (a b : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  {ω | HorizontalCrossing ω a b}

end TwoDim
end StatMech
